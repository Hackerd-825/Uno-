'use strict';
const $=s=>document.querySelector(s);
const el=(t,c,x)=>{const e=document.createElement(t);if(c)e.className=c;if(x!=null)e.textContent=x;return e};
const rnd=n=>{const u=new Uint32Array(1);crypto.getRandomValues(u);return u[0]%n};
const shuffle=a=>{for(let i=a.length-1;i>0;i--){const j=rnd(i+1);[a[i],a[j]]=[a[j],a[i]]}return a};
const COL={r:'#e5384b',y:'#f4b81c',g:'#2faa5b',b:'#2f6fe0',w:'#25252d'};
const SYM={s:'⊘',r:'⇄',d2:'+2',w:'✦',w4:'+4'};
const ok=(c,t,col)=>c.c==='w'||c.c===col||c.v===t.v;
const show=id=>document.querySelectorAll('.screen').forEach(s=>s.hidden=s.id!==id);
const toast=m=>$('#msg').textContent=m;
const clean=n=>String(n||'').replace(/[^\p{L}\p{N} _-]/gu,'').trim().slice(0,14)||'Joueur';
const myName=()=>clean($('#name').value);
const ALPHA='ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
const mkCode=()=>Array.from({length:6},()=>ALPHA[rnd(ALPHA.length)]).join('');

/* ---------- Moteur de jeu (tourne uniquement chez l'hôte) ---------- */
class Game{
  constructor(players){
    this.p=players;this.dir=1;this.turn=0;this.over=null;this.drew=-1;this.log='';
    this.deck=[];for(const c of'rygb'){this.deck.push({c,v:'0'});for(let v=1;v<=9;v++)this.deck.push({c,v:''+v},{c,v:''+v});for(const v of['s','r','d2'])this.deck.push({c,v},{c,v})}
    for(let i=0;i<4;i++)this.deck.push({c:'w',v:'w'},{c:'w',v:'w4'});
    shuffle(this.deck);this.disc=[];
    this.p.forEach(x=>x.hand=Array.from({length:7},()=>this.draw()));
    let t;do{t=this.draw();if(t.c==='w')this.deck.unshift(t)}while(t.c==='w');
    this.disc.push(t);this.top=t;this.col=t.c;
  }
  draw(){if(!this.deck.length&&this.disc.length>1){const t=this.disc.pop();this.deck=shuffle(this.disc);this.disc=[t]}return this.deck.pop()||{c:'w',v:'w'}}
  next(n=1){const L=this.p.length;return(((this.turn+this.dir*n)%L)+L)%L}
  play(s,i,col){
    if(this.over!==null||s!==this.turn)return;
    const h=this.p[s].hand,c=h[i];
    if(!c||!ok(c,this.top,this.col)||(c.c==='w'&&!'rygb'.includes(col)))return;
    h.splice(i,1);this.disc.push(c);this.top=c;this.col=c.c==='w'?col:c.c;this.drew=-1;
    this.log=this.p[s].name+' a joué';
    if(!h.length){this.over=s;return}
    let skip=0;
    if(c.v==='s')skip=1;
    else if(c.v==='r'){if(this.p.length===2)skip=1;else this.dir*=-1}
    else if(c.v==='d2'||c.v==='w4'){const t=this.next();for(let k=0;k<(c.v==='d2'?2:4);k++)this.p[t].hand.push(this.draw());skip=1}
    this.turn=this.next(1+skip);
  }
  pick(s){
    if(this.over!==null||s!==this.turn)return;
    if(this.drew===s){this.drew=-1;this.turn=this.next();return}
    const c=this.draw();this.p[s].hand.push(c);this.log=this.p[s].name+' a pioché';
    if(ok(c,this.top,this.col))this.drew=s;else this.turn=this.next();
  }
  view(s){return{me:s,hand:this.p[s].hand,pl:this.p.map(x=>({n:x.name,c:x.hand.length})),top:this.top,col:this.col,turn:this.turn,over:this.over,log:this.log}}
}

/* ---------- État réseau / session ---------- */
let srch=0,peer=null,conn=null,role=null,lobby=null,G=null,started=false,bt=0,lt=0,lastView=null,pendingWild=-1;

function reset(){
  srch++;
  clearTimeout(bt);clearTimeout(lt);
  try{peer&&peer.destroy()}catch{}
  peer=conn=role=lobby=G=lastView=null;started=false;
  $('#end').hidden=$('#picker').hidden=true;show('menu');
}

function update(){
  renderGame(G.view(0));
  lobby.players.forEach((p,s)=>{if(p.conn&&p.conn.open)p.conn.send({t:'s',v:G.view(s)})});
  if(G.over===null&&G.p[G.turn].bot){
    clearTimeout(bt);
    bt=setTimeout(()=>{const s=G.turn;if(G.over===null&&G.p[s].bot){botMove(s);update()}},900+rnd(600));
  }
}
function botMove(s){
  const h=G.p[s].hand,pl=h.map((_,i)=>i).filter(i=>ok(h[i],G.top,G.col));
  if(!pl.length){G.pick(s);return}
  const i=pl.find(k=>h[k].c!=='w')??pl[0];
  const cnt={r:0,y:0,g:0,b:0};h.forEach(c=>{if(c.c!=='w')cnt[c.c]++});
  G.play(s,i,Object.keys(cnt).sort((a,b)=>cnt[b]-cnt[a])[0]);
}
function startGame(){
  started=true;clearInterval(lt);lobby.cd=null;
  G=new Game(lobby.players);show('game');update();
}
function act(s,t,i,col){
  if(!G)return;
  if(t==='play')G.play(s,i,col);else G.pick(s);
  update();
}
function send(t,i,col){
  if(role==='host')act(0,t,i,col);
  else if(conn&&conn.open)conn.send({t,i,col});
}

/* ---------- Rendu ---------- */
function cardEl(c){
  const s=SYM[c.v]||c.v,e=el('div','card '+c.c),o=el('div','oval');
  o.appendChild(el('span','mid',s));e.append(o,el('span','cn tl',s),el('span','cn br',s));return e;
}
function renderGame(v){
  if(!v||!Array.isArray(v.hand)||!Array.isArray(v.pl))return;
  lastView=v;
  const o=$('#opps');o.replaceChildren();
  v.pl.forEach((p,i)=>{if(i===v.me)return;
    const d=el('div','opp'+(v.turn===i?' turn':''),String(p.n));
    d.appendChild(el('small','',p.c+(p.c===1?' carte — UNO !':' cartes')));o.appendChild(d)});
  $('#pile').replaceChildren(cardEl(v.top));$('#colbar').style.background=COL[v.col]||'#fff';
  const mine=v.turn===v.me&&v.over===null;
  $('#status').textContent=v.over!==null?'':mine?'À toi de jouer':'Tour de '+v.pl[v.turn].n;
  const h=$('#hand');h.replaceChildren();
  v.hand.forEach((c,i)=>{
    const e=cardEl(c),can=mine&&ok(c,v.top,v.col);
    if(can){e.classList.add('ok');e.tabIndex=0;e.setAttribute('role','button');
      const go=()=>{if(c.c==='w'){pendingWild=i;$('#picker').hidden=false}else send('play',i)};
      e.onclick=go;e.onkeydown=ev=>{if(ev.key==='Enter'||ev.key===' '){ev.preventDefault();go()}}}
    h.appendChild(e)});
  $('#deck').disabled=!mine;
  if(v.over!==null){$('#endT').textContent=v.over===v.me?'Tu as gagné !':v.pl[v.over].n+' a gagné';$('#end').hidden=false}
}
function drawLobby(names,max,cd,code,canStart,pub){
  show('lobby');$('#lTitle').textContent=pub?'Partie publique':'Partie privée';
  const u=$('#lList');u.replaceChildren();
  for(let i=0;i<max;i++){const f=i<names.length,s=el('li','slot'+(f?' full':''));
    s.append(el('b','av',f?names[i].slice(0,1).toUpperCase():'?'),el('span','',f?names[i]:'En attente d’un joueur…'));u.appendChild(s)}
  $('#codeBox').hidden=!code;if(code)$('#codeShow').textContent=code;
  $('#bStart').hidden=!canStart;$('#bStart').disabled=names.length<2;
  $('#cd').hidden=cd==null;$('#cd').textContent=cd==null?'':cd;$('#spin').hidden=cd!=null;
  $('#lInfo').textContent=cd!=null?'La partie commence…':names.length<2?(pub?'Recherche de joueurs…':'Partage le code pour inviter des joueurs.'):canStart?'Lance la partie quand tout le monde est là.':pub?'Plus de joueurs ? Sinon on démarre bientôt.':'L’hôte va lancer la partie.';
}

/* ---------- Réseau (WebRTC via PeerJS, l'hôte fait autorité) ---------- */
function lobbyBroadcast(){
  const names=lobby.players.map(p=>p.name),m={t:'l',n:names,max:lobby.max,cd:lobby.cd,code:lobby.code,pub:lobby.pub};
  lobby.players.forEach(p=>p.conn&&p.conn.open&&p.conn.send(m));
  drawLobby(names,lobby.max,lobby.cd,lobby.code,role==='host'&&!lobby.pub,lobby.pub);
}
function lobbyChanged(){
  clearInterval(lt);lobby.cd=null;
  if(lobby.players.length>=lobby.max){startGame();return}
  if(lobby.pub&&lobby.players.length>=2){
    lobby.cd=8;lt=setInterval(()=>{lobby.cd--;if(lobby.cd<=0)startGame();else lobbyBroadcast()},1000)}
  lobbyBroadcast();
}
function hostNet(id,max,pub,code){
  return new Promise((res,rej)=>{
    const p=new Peer(id);peer=p;p.on('error',rej);
    p.on('open',()=>{
      role='host';started=false;lobby={players:[{name:myName()}],max,code,pub,cd:null};res();lobbyChanged();
      p.on('connection',c=>{
        const me={name:'',conn:c};let joined=false;
        c.on('data',d=>{
          if(!d||typeof d!=='object')return;
          if(d.t==='hello'&&!joined){
            if(started||lobby.players.length>=max){c.send({t:'full'});setTimeout(()=>c.close(),300);return}
            joined=true;me.name=clean(d.n);lobby.players.push(me);lobbyChanged();return}
          if(joined&&started&&(d.t==='draw'||(d.t==='play'&&Number.isInteger(d.i))))act(lobby.players.indexOf(me),d.t,d.i,d.col)});
        c.on('close',()=>{
          if(!joined)return;
          if(!started){lobby.players.splice(lobby.players.indexOf(me),1);lobbyChanged()}
          else{me.bot=true;me.conn=null;me.name+=' (bot)';if(G&&G.over===null)update()}});
      });
    });
  });
}
function joinNet(id,timeout){
  return new Promise((res,rej)=>{
    const p=new Peer();let done=false,to=0;
    const fail=r=>{if(done)return;done=true;clearTimeout(to);try{p.destroy()}catch{};rej(r)};
    p.on('error',()=>fail('err'));
    p.on('open',()=>{
      const c=p.connect(id,{reliable:true});to=setTimeout(()=>fail('timeout'),timeout);
      c.on('open',()=>c.send({t:'hello',n:myName()}));
      c.on('data',d=>{
        if(!d||typeof d!=='object')return;
        if(d.t==='full'){fail('full');return}
        if(!done){done=true;clearTimeout(to);peer=p;conn=c;role='guest';res()}
        if(d.t==='l'&&Array.isArray(d.n)){const mx=Math.min(6,Math.max(2,+d.max||2));drawLobby(d.n.slice(0,6).map(clean),mx,Number.isInteger(d.cd)?d.cd:null,/^[A-Z0-9]{6}$/.test(d.code)?d.code:null,false,!!d.pub)}
        if(d.t==='s'){show('game');renderGame(d.v)}});
      c.on('close',()=>{if(!done)fail('closed');else if(role==='guest'&&!(lastView&&lastView.over!==null)){alert('L’hôte a quitté la partie.');reset()}});
    });
  });
}

/* ---------- Menu ---------- */
$('#name').value='Joueur'+(100+rnd(900));
$('#bBots').onclick=()=>{
  const n=Math.min(3,Math.max(1,+$('#nbots').value||2));
  role='host';started=false;
  lobby={players:[{name:myName()},...Array.from({length:n},(_,i)=>({name:'Bot '+(i+1),bot:true}))],max:n+1};
  startGame();
};
$('#bCreate').onclick=async()=>{
  toast('');
  for(let k=0;k<5;k++){
    const code=mkCode();
    try{await hostNet('unoz-'+code,Math.min(6,Math.max(2,+$('#pmax').value||2)),false,code);return}
    catch(e){try{peer.destroy()}catch{};if(e.type!=='unavailable-id'){toast('Connexion impossible. Réessaie.');return}}
  }
};
$('#bJoin').onclick=async()=>{
  const code=$('#code').value.toUpperCase().trim();
  if(!/^[A-Z0-9]{6}$/.test(code)){toast('Le code contient 6 lettres ou chiffres.');return}
  toast('Connexion…');
  try{await joinNet('unoz-'+code,8000);toast('')}
  catch(e){toast(e==='full'?'Cette partie est déjà complète.':'Code introuvable ou hôte hors ligne.')}
};
$('#bPub').onclick=async()=>{
  const my=++srch;toast('');drawLobby([],4,null,null,false,true);
  for(let i=0;i<12;i++){
    if(my!==srch)return;
    try{await hostNet('unopub-'+i,4,true);return}
    catch(e){try{peer.destroy()}catch{};if(e.type!=='unavailable-id'){toast('Connexion impossible. Réessaie.');return}}
    try{await joinNet('unopub-'+i,5000);if(my!==srch)reset();return}catch{}
  }
  if(my!==srch)return;show('menu');toast('Aucune partie libre trouvée. Réessaie.');
};
$('#bStart').onclick=()=>{if(role==='host'&&lobby&&!started&&lobby.players.length>=2)startGame()};
$('#bCancel').onclick=reset;$('#bEnd').onclick=reset;
$('#bCopy').onclick=()=>navigator.clipboard&&navigator.clipboard.writeText($('#codeShow').textContent).then(()=>$('#bCopy').textContent='Copié');
$('#deck').onclick=()=>send('draw');
const pc=$('#pcols');
for(const k of'rygb'){const b=el('button');b.style.background=COL[k];b.setAttribute('aria-label',{r:'Rouge',y:'Jaune',g:'Vert',b:'Bleu'}[k]);
  b.onclick=()=>{$('#picker').hidden=true;send('play',pendingWild,k)};pc.appendChild(b)}
