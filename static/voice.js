// Text-to-speech using the browser's built-in voices (no server, no cost). Browsers require one tap before speaking.
const Voice={on:false,ok:'speechSynthesis' in window,
  say(t){if(!this.on||!this.ok)return;const u=new SpeechSynthesisUtterance(t);u.lang='en-IN';u.rate=.95;speechSynthesis.speak(u)},
  bind(btn,label){
    if(!this.ok){btn.textContent='Voice is not supported in this browser';btn.disabled=true;return}
    const set=()=>{btn.textContent=this.on?'🔊 '+label+' on (tap to mute)':'🔇 Tap to enable '+label.toLowerCase();btn.setAttribute('aria-pressed',this.on)};
    btn.onclick=()=>{this.on=!this.on;if(this.on){speechSynthesis.cancel();speechSynthesis.speak(new SpeechSynthesisUtterance(label+' on'))}set()};set()}};
const spoken=n=>/^\d+$/.test(n)?n.split('').join(' '):n;   // read roll numbers digit by digit
