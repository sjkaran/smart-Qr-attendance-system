"""Dynamic-QR attendance: Flask + SQLite. Run: python app.py  (demo data seeded on first run)"""
import base64, hmac, hashlib, io, json, os, secrets, sqlite3, time
from collections import defaultdict, deque
from werkzeug.middleware.proxy_fix import ProxyFix
from functools import wraps
import pandas as pd
from flask import (Flask, g, redirect, render_template, request, send_file,
                   session, jsonify, url_for, flash, abort)
from werkzeug.security import generate_password_hash, check_password_hash
from cryptography.fernet import Fernet
from webauthn import (generate_registration_options, verify_registration_response, generate_authentication_options,
                      verify_authentication_response, options_to_json)
from webauthn.helpers import base64url_to_bytes, bytes_to_base64url
from webauthn.helpers.structs import (AuthenticatorSelectionCriteria, AuthenticatorAttachment, UserVerificationRequirement,
                                      ResidentKeyRequirement, PublicKeyCredentialDescriptor)

SLOT_MS = 500          # QR changes every 0.5 s
GRACE_SLOTS = int(os.environ.get("GRACE_SLOTS", 6))   # codes up to ~2 s old are accepted (phone + network latency)
CHECK_IP = os.environ.get("CHECK_IP", "0") == "1"   # require student on teacher's network
DB = os.environ.get("DB_PATH", "attendance.db")

app = Flask(__name__)
ON_RENDER = bool(os.environ.get("RENDER"))
if ON_RENDER and not os.environ.get("SECRET_KEY"): raise SystemExit("SECRET_KEY must be set in production")
app.secret_key = os.environ.get("SECRET_KEY", "dev-only-secret")
app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1)     # real client IP / https behind the host's proxy
app.config.update(SESSION_COOKIE_HTTPONLY=True, SESSION_COOKIE_SAMESITE="Lax", SESSION_COOKIE_SECURE=ON_RENDER)
INVITE = os.environ.get("FACULTY_INVITE", "")                 # secret code that lets a faculty member self-register
PASSKEY_REQUIRED = os.environ.get("REQUIRE_PASSKEY", "1" if ON_RENDER else "0") == "1"   # needs a real domain (not a LAN IP)
app.config["PERMANENT_SESSION_LIFETIME"] = 8 * 3600
def limited(key, n, per):               # rate limit stored in the database, so it holds across workers
    now = time.time()
    if secrets.randbelow(20) == 0: run("DELETE FROM hits WHERE t<?", now - 3600)
    if q1("SELECT COUNT(*) AS n FROM hits WHERE k=? AND t>?", str(key), now - per)["n"] >= n: return True
    run("INSERT INTO hits VALUES(?,?)", str(key), now); return False

SCHEMA = """
CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY, username TEXT UNIQUE, pw TEXT,
  name TEXT, role TEXT, roll_no TEXT UNIQUE);
CREATE TABLE IF NOT EXISTS subjects(id INTEGER PRIMARY KEY, name TEXT, teacher_id INTEGER);
CREATE TABLE IF NOT EXISTS enrollments(subject_id INTEGER, student_id INTEGER, UNIQUE(subject_id, student_id));
CREATE TABLE IF NOT EXISTS sessions(id INTEGER PRIMARY KEY, subject_id INTEGER, secret TEXT,
  started_at REAL, ended_at REAL, teacher_ip TEXT);
CREATE TABLE IF NOT EXISTS attendance(session_id INTEGER, student_id INTEGER, marked_at REAL,
  UNIQUE(session_id, student_id));
CREATE TABLE IF NOT EXISTS credentials(id INTEGER PRIMARY KEY, user_id INTEGER UNIQUE, cred_id TEXT UNIQUE, public_key TEXT, sign_count INTEGER, created REAL);
CREATE TABLE IF NOT EXISTS challenges(id TEXT PRIMARY KEY, user_id INTEGER, purpose TEXT, challenge TEXT, payload TEXT, expires REAL, used INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS audit(id INTEGER PRIMARY KEY, ts REAL, actor TEXT, event TEXT, detail TEXT, prev TEXT, hash TEXT);
CREATE TABLE IF NOT EXISTS hits(k TEXT, t REAL);
CREATE INDEX IF NOT EXISTS hits_k ON hits(k, t);
"""

PG = bool(os.environ.get("DATABASE_URL"))
if PG:
    import psycopg2, psycopg2.extras
    DBERR = (sqlite3.IntegrityError, psycopg2.IntegrityError)
else:
    DBERR = (sqlite3.IntegrityError,)

def connect():
    if PG: return psycopg2.connect(os.environ["DATABASE_URL"], cursor_factory=psycopg2.extras.RealDictCursor)
    c = sqlite3.connect(DB, timeout=10); c.row_factory = sqlite3.Row; return c

def fix(sql):                      # one SQL dialect for both SQLite (local) and Postgres (hosted)
    if not PG: return sql
    sql = sql.replace("?", "%s")
    if sql.lstrip().upper().startswith("INSERT OR IGNORE"):
        sql = sql.replace("INSERT OR IGNORE", "INSERT", 1) + " ON CONFLICT DO NOTHING"
    return sql

def exe(c, sql, a=(), ret=False):
    sql = fix(sql)
    if PG:
        cur = c.cursor(); cur.execute(sql + (" RETURNING id" if ret else ""), a); return cur
    return c.execute(sql, a)

def db():
    if "db" not in g: g.db = connect()
    return g.db

@app.teardown_appcontext
def close_db(_):
    d = g.pop("db", None)
    if d: d.close()

def q(sql, *a): return exe(db(), sql, a).fetchall()
def q1(sql, *a): return exe(db(), sql, a).fetchone()
class R:
    def __init__(s, cur, ret): s.rowcount = cur.rowcount; s.lastrowid = (cur.fetchone()["id"] if PG else cur.lastrowid) if ret else None
def run(sql, *a, ret=False):
    r = R(exe(db(), sql, a, ret), ret); db().commit(); return r

@app.get("/healthz")
def healthz(): return "ok"

def login_required(role):
    def deco(f):
        @wraps(f)
        def w(*a, **k):
            if session.get("role") != role:
                if request.path.startswith("/api/"): return jsonify(ok=False, msg="You are logged out. Log in again."), 401
                return redirect(url_for("login"))
            return f(*a, **k)
        return w
    return deco

# ---------- QR token logic ----------
def now_slot(): return int(time.time() * 1000) // SLOT_MS
def sign(secret, sid, slot):
    return hmac.new(secret.encode(), f"{sid}.{slot}".encode(), hashlib.sha256).hexdigest()[:12]

# ---------- security core: CSRF, headers, audit chain, one-time challenges ----------
@app.before_request
def csrf_guard():
    if "csrf" not in session: session["csrf"] = secrets.token_hex(16)
    if request.method == "POST":
        sent = request.form.get("_csrf") or request.headers.get("X-CSRF-Token", "")
        if not hmac.compare_digest(sent, session["csrf"]): abort(400)

@app.context_processor
def inject_csrf(): return {"csrf_token": session.get("csrf", ""), "faculty_signup": bool(INVITE)}

@app.after_request
def secure_headers(r):
    r.headers.update({"X-Content-Type-Options": "nosniff", "X-Frame-Options": "DENY", "Referrer-Policy": "same-origin",
        "Permissions-Policy": "camera=(self), publickey-credentials-get=(self), publickey-credentials-create=(self)",
        "Content-Security-Policy": "default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'; "
                                   "img-src 'self' data:; media-src 'self' blob:; connect-src 'self'; frame-ancestors 'none'; base-uri 'self'; form-action 'self'"})
    if ON_RENDER: r.headers["Strict-Transport-Security"] = "max-age=31536000"
    if request.path.startswith("/api/"): r.headers["Cache-Control"] = "no-store"
    return r

def audit(event, actor="", detail=""):
    """Append-only, hash-chained log: each row commits to the previous one, so edits are detectable."""
    c = db()
    if PG: exe(c, "LOCK TABLE audit IN EXCLUSIVE MODE", ())
    last = q1("SELECT hash FROM audit ORDER BY id DESC LIMIT 1")
    prev = last["hash"] if last else "0" * 64; ts = round(time.time(), 3)
    h = hashlib.sha256(f"{prev}|{ts:.3f}|{actor}|{event}|{detail}".encode()).hexdigest()
    exe(c, "INSERT INTO audit(ts,actor,event,detail,prev,hash) VALUES(?,?,?,?,?,?)", (ts, str(actor), event, str(detail), prev, h)); c.commit()

def audit_verify():
    prev = "0" * 64
    for r in q("SELECT * FROM audit ORDER BY id"):
        h = hashlib.sha256(f"{prev}|{r['ts']:.3f}|{r['actor']}|{r['event']}|{r['detail']}".encode()).hexdigest()
        if r["prev"] != prev or r["hash"] != h: return False, r["id"]
        prev = r["hash"]
    return True, None

def new_challenge(uid, purpose, payload=None, ttl=60):
    ch, cid = secrets.token_bytes(32), secrets.token_urlsafe(16)
    run("INSERT INTO challenges(id,user_id,purpose,challenge,payload,expires,used) VALUES(?,?,?,?,?,?,0)",
        cid, uid, purpose, bytes_to_base64url(ch), payload, time.time() + ttl)
    return cid, ch

def take_challenge(cid, uid, purpose):          # single use, bound to the user and the purpose
    r = q1("SELECT * FROM challenges WHERE id=? AND user_id=? AND purpose=? AND used=0 AND expires>?", cid or "", uid, purpose, time.time())
    return r if r and run("UPDATE challenges SET used=1 WHERE id=? AND used=0", cid).rowcount == 1 else None

def rp(): return os.environ.get("RP_ID") or os.environ.get("RENDER_EXTERNAL_HOSTNAME") or request.host.split(":")[0]
def origin(): return os.environ.get("ORIGIN") or (f"https://{rp()}" if ON_RENDER else f"{request.scheme}://{request.host}")
def new_code(): return "".join(secrets.choice("ABCDEFGHJKMNPQRSTUVWXYZ23456789") for _ in range(8))
def _fernet(): return Fernet(base64.urlsafe_b64encode(hashlib.sha256(app.secret_key.encode()).digest()))
def enc_code(code): return _fernet().encrypt(code.encode()).decode()     # pending codes are stored encrypted so faculty can view them
def dec_code(tok):
    try: return _fernet().decrypt(tok.encode()).decode() if tok else None
    except Exception: return None

def code_hash(roll, code): return hmac.new(app.secret_key.encode(), f"{roll.upper()}|{code.upper()}".encode(), hashlib.sha256).hexdigest()

def import_roster(sid, df):
    """Enroll roll numbers. Students without an active account get one plus a one-time activation code
    (taken from an optional 'code' column, otherwise random). Names come from any column containing 'name'."""
    df = df.copy(); df.columns = [str(c).strip().lower() for c in df.columns]
    col = next(c for c in df.columns if c in ("roll_no", "roll no", "roll", "roll number"))
    ncol = next((c for c in df.columns if "name" in c), None)
    ccol = next((c for c in df.columns if c.replace(" ", "_") in ("code", "activation_code")), None)
    counts = df[ccol].dropna().astype(str).str.strip().str.upper().value_counts() if ccol else {}
    out = dict(enrolled=0, codes=[], notes=[], name_col=ncol is not None)
    for i, roll in df[col].items():
        if pd.isna(roll): continue
        roll = str(roll).strip(); roll = roll[:-2] if roll.endswith(".0") else roll
        if not roll: continue
        nm = str(df[ncol][i]).strip() if ncol and not pd.isna(df[ncol][i]) and str(df[ncol][i]).strip() else roll
        given = None
        if ccol and not pd.isna(df[ccol][i]) and str(df[ccol][i]).strip():
            g = str(df[ccol][i]).strip()
            if len(g) >= 6 and g.isalnum() and counts.get(g.upper(), 0) == 1: given = g
            else: out["notes"].append(f"{roll}: your custom code was not used (it needs 6+ letters or digits and must differ for every student), so a random one was created.")
        u = q1("SELECT * FROM users WHERE UPPER(roll_no)=UPPER(?) AND role='student'", roll)
        if not u or not u["pw"]:
            code = given or (dec_code(u["act_enc"]) if u else None) or new_code(); h = code_hash(roll, code)
            if u:
                nm = nm if nm != roll else u["name"]; uid = u["id"]
                run("UPDATE users SET act_hash=?, act_enc=?, name=? WHERE id=?", h, enc_code(code), nm, uid)
            else:
                try: uid = run("INSERT INTO users(username,pw,name,role,roll_no,act_hash,act_enc) VALUES(?,?,?,?,?,?,?)", roll.lower(), None, nm, "student", roll, h, enc_code(code), ret=True).lastrowid
                except DBERR: db().rollback(); uid = run("INSERT INTO users(username,pw,name,role,roll_no,act_hash,act_enc) VALUES(?,?,?,?,?,?,?)", f"{roll.lower()}-{secrets.token_hex(2)}", None, nm, "student", roll, h, enc_code(code), ret=True).lastrowid
            out["codes"].append((roll, nm, code))
        else: uid = u["id"]
        run("INSERT OR IGNORE INTO enrollments VALUES(?,?)", sid, uid); out["enrolled"] += 1
    return out

# ---------- auth ----------
@app.route("/")
def index():
    return redirect(url_for("teacher_home" if session.get("role") == "teacher" else
                            "student_home" if session.get("role") == "student" else "login"))

@app.route("/login", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        if limited("login:" + str(request.remote_addr), 10, 60) or limited("loginu:" + request.form.get("username", "").strip().lower(), 8, 300):
            flash("Too many attempts. Wait a minute."); return render_template("login.html")
        ident = request.form.get("username", "").strip()
        u = q1("SELECT * FROM users WHERE LOWER(username)=LOWER(?) OR (role='student' AND UPPER(roll_no)=UPPER(?)) LIMIT 1", ident, ident)
        if u and u["pw"] and check_password_hash(u["pw"], request.form["password"]):
            session.clear(); session.update(uid=u["id"], role=u["role"], name=u["name"]); session.permanent = True; audit("login", u["username"], request.remote_addr)
            return redirect(url_for("index"))
        audit("login_failed", request.form.get("username", "")[:40], request.remote_addr); flash("Wrong username or password.")
    return render_template("login.html")

@app.route("/register", methods=["GET", "POST"])
def register():                       # faculty only; students activate from the roster
    if not INVITE: abort(404)
    if request.method == "POST":
        f = request.form
        teacher = bool(INVITE) and hmac.compare_digest(f.get("invite", "").strip(), INVITE)
        roll = f.get("roll_no", "").strip() or None
        if not teacher:
            flash("A valid faculty invite code is required. Students activate their account from the roster."); return render_template("register.html", invite=True)
        try:
            run("INSERT INTO users(username,pw,name,role,roll_no) VALUES(?,?,?,?,?)",
                f["username"].strip(), generate_password_hash(f["password"]), f["name"].strip(),
                "teacher" if teacher else "student", None if teacher else roll)
            flash("Account created. Log in to continue."); return redirect(url_for("login"))
        except DBERR:
            db().rollback(); flash("That username or roll number is already registered.")
    return render_template("register.html", invite=bool(INVITE))

@app.route("/logout")
def logout():
    session.clear(); return redirect(url_for("login"))

# ---------- teacher ----------
@app.route("/teacher")
@login_required("teacher")
def teacher_home():
    subs = q("""SELECT s.*, (SELECT COUNT(*) FROM enrollments e WHERE e.subject_id=s.id) AS n_students,
      (SELECT COUNT(*) FROM sessions x WHERE x.subject_id=s.id) AS n_sessions,
      (SELECT id FROM sessions x WHERE x.subject_id=s.id AND x.ended_at IS NULL) AS live_id
      FROM subjects s WHERE teacher_id=?""", session["uid"])
    return render_template("teacher.html", subjects=subs)

@app.post("/teacher/subject")
@login_required("teacher")
def add_subject():
    run("INSERT INTO subjects(name,teacher_id) VALUES(?,?)", request.form["name"].strip(), session["uid"])
    return redirect(url_for("teacher_home"))

def own_subject(sid):
    s = q1("SELECT * FROM subjects WHERE id=? AND teacher_id=?", sid, session["uid"])
    return s or abort(404)

@app.post("/teacher/subject/<int:sid>/roster")
@login_required("teacher")
def upload_roster(sid):
    own_subject(sid)
    try:
        f = request.files["file"]
        r = import_roster(sid, pd.read_csv(f, dtype=str) if f.filename.lower().endswith(".csv") else pd.read_excel(f, dtype=str))
    except Exception:
        flash("Upload an .xlsx or .csv file with a 'roll' column (plus 'name' and optional 'code')."); return redirect(url_for("teacher_home"))
    audit("roster_upload", session["name"], f"subject={sid} enrolled={r['enrolled']} new_accounts={len(r['codes'])}")
    return render_template("codes.html", r=r)

@app.post("/teacher/subject/<int:sid>/start")
@login_required("teacher")
def start_session(sid):
    own_subject(sid)
    live = q1("SELECT id FROM sessions WHERE subject_id=? AND ended_at IS NULL", sid)
    if live: return redirect(url_for("live_session", xid=live["id"]))
    c = run("INSERT INTO sessions(subject_id,secret,started_at,teacher_ip) VALUES(?,?,?,?)",
            sid, secrets.token_hex(16), time.time(), request.remote_addr, ret=True)
    return redirect(url_for("live_session", xid=c.lastrowid))

def own_session(xid):
    s = q1("""SELECT x.*, s.name AS subject FROM sessions x JOIN subjects s ON s.id=x.subject_id
              WHERE x.id=? AND s.teacher_id=?""", xid, session["uid"])
    return s or abort(404)

@app.route("/teacher/session/<int:xid>")
@login_required("teacher")
def live_session(xid):
    return render_template("session.html", s=own_session(xid), slot_ms=SLOT_MS)

@app.get("/api/session/<int:xid>/tokens")
@login_required("teacher")
def tokens(xid):
    s = own_session(xid)
    if s["ended_at"]: return jsonify(ended=True)
    start = now_slot()
    return jsonify(server_ms=int(time.time() * 1000), slot_ms=SLOT_MS,
                   tokens={str(sl): sign(s["secret"], xid, sl) for sl in range(start, start + 40)})

@app.get("/api/session/<int:xid>/live")
@login_required("teacher")
def live(xid):
    own_session(xid)
    rows = q("""SELECT u.name, u.roll_no, a.marked_at FROM attendance a JOIN users u ON u.id=a.student_id
                WHERE a.session_id=? ORDER BY a.marked_at DESC""", xid)
    tot = q1("""SELECT COUNT(*) c FROM enrollments WHERE subject_id=(SELECT subject_id FROM sessions WHERE id=?)""", xid)["c"]
    return jsonify(total=tot, present=[dict(r) for r in rows])

@app.post("/teacher/session/<int:xid>/end")
@login_required("teacher")
def end_session(xid):
    own_session(xid); run("UPDATE sessions SET ended_at=? WHERE id=?", time.time(), xid)
    return redirect(url_for("teacher_home"))

def matrix(sid):
    """Rows = students, columns = sessions, plus totals. Shared by the Excel export."""
    sess = q("SELECT id, started_at FROM sessions WHERE subject_id=? ORDER BY started_at", sid)
    studs = q("""SELECT u.id, u.roll_no, u.name FROM enrollments e JOIN users u ON u.id=e.student_id
                 WHERE e.subject_id=? ORDER BY u.roll_no""", sid)
    marks = {(r["session_id"], r["student_id"]) for r in
             q("SELECT session_id, student_id FROM attendance WHERE session_id IN (SELECT id FROM sessions WHERE subject_id=?)", sid)}
    rows = []
    for st in studs:
        row = {"Roll No": st["roll_no"], "Name": st["name"]}; n = 0
        for x in sess:
            p = (x["id"], st["id"]) in marks; n += p
            row[time.strftime("%d-%b %H:%M", time.localtime(x["started_at"]))] = "P" if p else "A"
        row["Attended"] = n; row["Total"] = len(sess)
        row["Percent"] = round(100 * n / len(sess), 1) if sess else 0
        rows.append(row)
    return pd.DataFrame(rows)

@app.route("/teacher/subject/<int:sid>/export.xlsx")
@login_required("teacher")
def export(sid):
    s = own_subject(sid); buf = io.BytesIO()
    matrix(sid).to_excel(buf, index=False, sheet_name="Attendance"); buf.seek(0)
    return send_file(buf, as_attachment=True, download_name=f"{s['name']}_attendance.xlsx",
                     mimetype="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")

# ---------- student ----------
def student_stats(uid):
    return q("""SELECT s.id, s.name,
      (SELECT COUNT(*) FROM sessions x WHERE x.subject_id=s.id) AS total,
      (SELECT COUNT(*) FROM attendance a JOIN sessions x ON x.id=a.session_id
         WHERE x.subject_id=s.id AND a.student_id=?) AS attended
      FROM subjects s JOIN enrollments e ON e.subject_id=s.id WHERE e.student_id=?""", uid, uid)

@app.route("/student")
@login_required("student")
def student_home():
    subs = [dict(r, pct=round(100 * r["attended"] / r["total"]) if r["total"] else 0) for r in student_stats(session["uid"])]
    live = q("""SELECT s.name FROM sessions x JOIN subjects s ON s.id=x.subject_id
                JOIN enrollments e ON e.subject_id=s.id WHERE x.ended_at IS NULL AND e.student_id=?""", session["uid"])
    return render_template("student.html", subjects=subs, live=live,
                           needs_key=PASSKEY_REQUIRED and not q1("SELECT 1 FROM credentials WHERE user_id=?", session["uid"]))

@app.route("/student/report/<int:sid>")
@login_required("student")
def student_report(sid):
    if not q1("SELECT 1 FROM enrollments WHERE subject_id=? AND student_id=?", sid, session["uid"]): abort(404)
    sub = q1("SELECT * FROM subjects WHERE id=?", sid)
    rows = q("""SELECT x.started_at, a.marked_at IS NOT NULL AS present FROM sessions x
                LEFT JOIN attendance a ON a.session_id=x.id AND a.student_id=? WHERE x.subject_id=?
                ORDER BY x.started_at DESC""", session["uid"], sid)
    hist = [dict(date=time.strftime("%a %d %b, %H:%M", time.localtime(r["started_at"])), present=bool(r["present"])) for r in rows]
    n = sum(h["present"] for h in hist)
    return render_template("report.html", sub=sub, hist=hist, n=n, total=len(hist),
                           pct=round(100 * n / len(hist)) if hist else 0)

@app.route("/student/scan")
@login_required("student")
def scan_page():
    if PASSKEY_REQUIRED and not q1("SELECT 1 FROM credentials WHERE user_id=?", session["uid"]): return redirect(url_for("passkey_page"))
    return render_template("scan.html", pk=PASSKEY_REQUIRED)

# ---------- activation, passkeys, device management ----------
@app.route("/activate", methods=["GET", "POST"])
def activate():
    if request.method == "POST":
        f = request.form; roll = f.get("roll_no", "").strip()
        if limited("act:" + str(request.remote_addr), 10, 300) or limited("actr:" + roll.upper(), 8, 600):
            flash("Too many attempts. Wait a few minutes."); return render_template("activate.html")
        u = q1("SELECT * FROM users WHERE UPPER(roll_no)=UPPER(?) AND role='student' AND pw IS NULL", roll)
        if not (u and u["act_hash"] and hmac.compare_digest(u["act_hash"], code_hash(roll, f.get("code", "").strip())) and len(f.get("password", "")) >= 8):
            audit("activation_failed", roll[:30], request.remote_addr)
            flash("Invalid roll number or code, or the password is shorter than 8 characters."); return render_template("activate.html")
        run("UPDATE users SET pw=?, act_hash=NULL, act_enc=NULL WHERE id=?", generate_password_hash(f["password"]), u["id"])
        session.clear(); session.update(uid=u["id"], role="student", name=u["name"]); session.permanent = True
        audit("activated", u["roll_no"]); return redirect(url_for("passkey_page" if PASSKEY_REQUIRED else "student_home"))
    return render_template("activate.html")

@app.route("/student/passkey")
@login_required("student")
def passkey_page():
    return render_template("passkey.html", has=bool(q1("SELECT 1 FROM credentials WHERE user_id=?", session["uid"])), on=PASSKEY_REQUIRED)

@app.post("/api/passkey/register/options")
@login_required("student")
def pk_reg_options():
    uid = session["uid"]
    if q1("SELECT 1 FROM credentials WHERE user_id=?", uid):
        return jsonify(ok=False, msg="A passkey is already registered. Ask faculty to reset it."), 409
    cid, ch = new_challenge(uid, "reg")
    opts = generate_registration_options(rp_id=rp(), rp_name="QR Attendance", user_id=str(uid).encode(), user_name=session["name"],
        user_display_name=session["name"], challenge=ch, authenticator_selection=AuthenticatorSelectionCriteria(
            authenticator_attachment=AuthenticatorAttachment.PLATFORM, resident_key=ResidentKeyRequirement.DISCOURAGED,
            user_verification=UserVerificationRequirement.REQUIRED))
    return jsonify(cid=cid, options=json.loads(options_to_json(opts)))

@app.post("/api/passkey/register/verify")
@login_required("student")
def pk_reg_verify():
    d = request.get_json(silent=True) or {}; uid = session["uid"]
    ch = take_challenge(d.get("cid"), uid, "reg")
    if not ch: return jsonify(ok=False, msg="That request expired. Try again."), 400
    try:
        v = verify_registration_response(credential=d["credential"], expected_challenge=base64url_to_bytes(ch["challenge"]),
            expected_rp_id=rp(), expected_origin=origin(), require_user_verification=True)
        run("INSERT INTO credentials(user_id,cred_id,public_key,sign_count,created) VALUES(?,?,?,?,?)",
            uid, bytes_to_base64url(v.credential_id), bytes_to_base64url(v.credential_public_key), v.sign_count, time.time())
    except DBERR:
        db().rollback(); return jsonify(ok=False, msg="A passkey is already registered."), 409
    except Exception:
        audit("passkey_register_failed", session["name"], request.remote_addr); return jsonify(ok=False, msg="Could not verify this device."), 400
    audit("passkey_registered", session["name"], request.remote_addr)
    return jsonify(ok=True, msg="Passkey saved. You can now mark attendance.")

@app.route("/teacher/subject/<int:sid>/students")
@login_required("teacher")
def students(sid):
    s = own_subject(sid)
    rows = q("""SELECT u.id, u.roll_no, u.name, (u.pw IS NOT NULL) AS active,
      (SELECT COUNT(*) FROM credentials c WHERE c.user_id=u.id) AS n_keys, u.act_enc FROM enrollments e
      JOIN users u ON u.id=e.student_id WHERE e.subject_id=? ORDER BY u.roll_no""", sid)
    rows = [dict(r, code=dec_code(r["act_enc"]) if not r["active"] else None) for r in rows]
    if any(r["code"] for r in rows): audit("codes_viewed", session["name"], f"subject={sid}")
    return render_template("students.html", s=s, rows=rows, on=PASSKEY_REQUIRED)

@app.post("/teacher/student/<int:uid>/reset")
@login_required("teacher")
def reset_passkey(uid):
    own = q1("""SELECT e.subject_id FROM enrollments e JOIN subjects s ON s.id=e.subject_id
                WHERE e.student_id=? AND s.teacher_id=? LIMIT 1""", uid, session["uid"])
    if not own: abort(404)
    run("DELETE FROM credentials WHERE user_id=?", uid); audit("passkey_reset", session["name"], f"student_id={uid}")
    flash("Passkey removed. The student can register a new one when signed in."); return redirect(url_for("students", sid=own["subject_id"]))

@app.post("/teacher/student/<int:uid>/newcode")
@login_required("teacher")
def new_activation_code(uid):
    own = q1("""SELECT e.subject_id, u.roll_no, u.pw FROM enrollments e JOIN subjects s ON s.id=e.subject_id JOIN users u ON u.id=e.student_id
                WHERE e.student_id=? AND s.teacher_id=? LIMIT 1""", uid, session["uid"])
    if not own or own["pw"]: abort(404)                     # only for students who have not activated yet
    code = new_code(); run("UPDATE users SET act_hash=?, act_enc=? WHERE id=?", code_hash(own["roll_no"], code), enc_code(code), uid)
    audit("code_reissued", session["name"], f"student_id={uid}"); flash(f"New activation code for {own['roll_no']}: {code}")
    return redirect(url_for("students", sid=own["subject_id"]))

@app.get("/teacher/audit.json")
@login_required("teacher")
def audit_json():
    ok, bad = audit_verify()
    rows = q("SELECT id, ts, actor, event, detail FROM audit ORDER BY id DESC LIMIT 100")
    return jsonify(chain_intact=ok, first_bad_row=bad, latest=[dict(r) for r in rows])

def check_payload(payload, received):
    """Validate a scanned QR. Returns (session_row, error, age_in_slots). `received` is stamped on arrival."""
    try:
        tag, sid, slot, sig = str(payload).split("."); sid, slot = int(sid), int(slot)
    except Exception:
        return None, "That's not an attendance QR code.", 0
    s = q1("SELECT * FROM sessions WHERE id=?", sid)
    if tag != "SQA1" or not s or s["ended_at"]: return None, "This class session isn't open.", 0
    if not hmac.compare_digest(sig, sign(s["secret"], sid, slot)): return None, "Invalid QR code.", 0
    age = received - slot
    if abs(age) > GRACE_SLOTS: return None, f"Code expired ({abs(age) * SLOT_MS / 1000:.1f}s old). Scan the live screen, not a photo.", age
    if not q1("SELECT 1 FROM enrollments WHERE subject_id=? AND student_id=?", s["subject_id"], session["uid"]):
        return None, "You're not enrolled in this subject.", age
    if CHECK_IP and request.remote_addr != s["teacher_ip"]: return None, "Join the classroom network to mark attendance.", age
    return s, None, age

def reason_of(err): return "not_enrolled" if "not enrolled" in err else "rejected"

def subject_name(s): return q1("SELECT name FROM subjects WHERE id=?", s["subject_id"])["name"]

@app.post("/api/scan")                     # cookie-only mode: used only when passkeys are off (local/LAN use)
@login_required("student")
def scan():
    received = now_slot()
    if PASSKEY_REQUIRED: return jsonify(ok=False, msg="Passkey confirmation is required."), 403
    if limited(f"scan:{session['uid']}", 40, 10): return jsonify(ok=False, msg="Slow down."), 429
    s, err, age = check_payload((request.get_json(silent=True) or {}).get("payload"), received)
    if err: return jsonify(ok=False, msg=err, reason=reason_of(err)), 400
    c = run("INSERT OR IGNORE INTO attendance VALUES(?,?,?)", s["id"], session["uid"], time.time())
    audit("scan_ok_nopasskey", session["name"], f"session={s['id']} age_slots={age}")
    return jsonify(ok=True, msg=f"Attendance marked for {subject_name(s)}." if c.rowcount else f"Already marked for {subject_name(s)}.", already=not c.rowcount)

@app.post("/api/scan/begin")               # step 1: QR is fresh + student enrolled -> issue a one-time passkey challenge
@login_required("student")
def scan_begin():
    received = now_slot(); uid = session["uid"]
    if limited(f"scan:{uid}", 40, 10): return jsonify(ok=False, msg="Slow down."), 429
    cred = q1("SELECT cred_id FROM credentials WHERE user_id=?", uid)
    if not cred: return jsonify(ok=False, msg="Set up your passkey first.", setup=True), 403
    s, err, age = check_payload((request.get_json(silent=True) or {}).get("payload"), received)
    if err:
        audit("scan_rejected", session["name"], f"{err} age_slots={age}"); return jsonify(ok=False, msg=err, reason=reason_of(err)), 400
    cid, ch = new_challenge(uid, "scan", payload=f"{s['id']}:{age}", ttl=30)
    opts = generate_authentication_options(rp_id=rp(), challenge=ch, user_verification=UserVerificationRequirement.REQUIRED,
        allow_credentials=[PublicKeyCredentialDescriptor(id=base64url_to_bytes(cred["cred_id"]))])
    return jsonify(cid=cid, options=json.loads(options_to_json(opts)))

@app.post("/api/scan/finish")              # step 2: passkey signature over our challenge proves the right student's device + unlock
@login_required("student")
def scan_finish():
    d = request.get_json(silent=True) or {}; uid = session["uid"]
    ch = take_challenge(d.get("cid"), uid, "scan")
    if not ch: return jsonify(ok=False, msg="That check expired. Scan again."), 400
    cred = q1("SELECT * FROM credentials WHERE user_id=?", uid)
    try:
        v = verify_authentication_response(credential=d["credential"], expected_challenge=base64url_to_bytes(ch["challenge"]),
            expected_rp_id=rp(), expected_origin=origin(), credential_public_key=base64url_to_bytes(cred["public_key"]),
            credential_current_sign_count=cred["sign_count"], require_user_verification=True)
    except Exception:
        audit("scan_rejected", session["name"], "passkey check failed"); return jsonify(ok=False, msg="Identity check failed."), 403
    run("UPDATE credentials SET sign_count=? WHERE id=?", v.new_sign_count, cred["id"])
    sid, age = ch["payload"].split(":"); s = q1("SELECT * FROM sessions WHERE id=?", int(sid))
    if not s or s["ended_at"]: return jsonify(ok=False, msg="This class session just closed."), 400
    c = run("INSERT OR IGNORE INTO attendance VALUES(?,?,?)", s["id"], uid, time.time())
    audit("scan_ok", session["name"], f"session={sid} age_slots={age} ip={request.remote_addr}")
    return jsonify(ok=True, msg=f"Attendance marked for {subject_name(s)}." if c.rowcount else f"Already marked for {subject_name(s)}.", already=not c.rowcount)

def init():
    ddl = SCHEMA.replace("INTEGER PRIMARY KEY", "SERIAL PRIMARY KEY").replace("REAL", "DOUBLE PRECISION") if PG else SCHEMA
    c = connect()
    for stmt in ddl.split(";"):
        if stmt.strip(): exe(c, stmt)
    c.commit()
    for col in ("act_hash", "act_enc"):                                      # upgrade older databases
        try: exe(c, "ALTER TABLE users ADD COLUMN " + ("IF NOT EXISTS " if PG else "") + col + " TEXT"); c.commit()
        except Exception: c.rollback()
    u, p = os.environ.get("FACULTY_USER"), os.environ.get("FACULTY_PASS")   # first faculty account (no shell on free hosts)
    if u and p:
        exe(c, "INSERT OR IGNORE INTO users(username,pw,name,role) VALUES(?,?,?,'teacher')",
            (u, generate_password_hash(p), os.environ.get("FACULTY_NAME", "Faculty")))
    c.commit(); c.close()

init()   # runs once at import (gunicorn --preload)

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)), ssl_context="adhoc" if os.environ.get("HTTPS") == "1" else None)
