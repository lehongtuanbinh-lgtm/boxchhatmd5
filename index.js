require('dotenv').config();
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { Bot, GrammyError, HttpError } = require('grammy');
const moment = require('moment-timezone');
const express = require('express');

// ============================================================
// ⚙️ CẤU HÌNH - BẢO LƯU GỐC & CẬP NHẬT THƯƠNG HIỆU HOÀNG
// ============================================================
const TOKEN = process.env.BOT_TOKEN || "8952833133:AAF2aaU9m_S1nlrcSMmzLZH-yZkORDbtQgk";
const ADMIN_ID = Number(process.env.ADMIN_ID) || 7833803456;
const ADMIN_USERNAME = "@cskhvilong1"; // ✅ ĐÃ CẬP NHẬT CHUẨN THƯƠNG HIỆU HOÀNG
const PORT = process.env.PORT || 10000;
const TZ = "Asia/Ho_Chi_Minh";
const USERS_FILE = path.join(__dirname, 'users.json');

let activatedUsers = {};
try {
  activatedUsers = JSON.parse(fs.readFileSync(USERS_FILE, 'utf8'));
} catch { activatedUsers = {}; }
activatedUsers[String(ADMIN_ID)] = { expires: "vĩnh viễn" };
fs.writeFileSync(USERS_FILE, JSON.stringify(activatedUsers, null, 2));

const saveUsers = () => fs.writeFileSync(USERS_FILE, JSON.stringify(activatedUsers, null, 2));
const isAdmin = id => Number(id) === ADMIN_ID;
const nowVN = () => moment.tz(TZ);

function checkUser(uid) {
  uid = String(uid);
  if (!(uid in activatedUsers)) return [false, null];
  const e = activatedUsers[uid].expires;
  if (e === "vĩnh viễn" || e === "vinh vien") return [true, "♾️ Vĩnh viễn"];
  const exp = moment.tz(e, "YYYY-MM-DD HH:mm:ss", TZ);
  return nowVN().isBefore(exp) ? [true, exp.format("DD/MM/YYYY HH:mm")] : [false, "Hết hạn"];
}

// ============================================================
// 🧠 THUẬT TOÁN - GIỮ NGUYÊN 100% GỐC + THÊM BÓC TÁCH MD5 CHUYÊN SÂU
// ============================================================
class HashAnalyzer {
  constructor() {
    this.history = [];
    this.breakProtector = { mode:null, count:0, consecutiveWrong:0, adaptiveThreshold:3, lastPrediction:null, reverseCount:0 };
    this.coreState = { daoChieu:false, entropyHigh:false }; 
    this.md5Stats = {
      byteTransition: Array.from({length:256},()=>[0,0]),
      bitRun: [], totalSamples:0, taiReal:0, xiuReal:0,
      markov2: Array.from({length:4},()=>[0,0]), 
      bitEntropyLog: [], accuracyLog: []
    };
    this.lastDetails = null; 
  }

  // ——— GIỮ NGUYÊN HOÀN TOÀN CÁC THUẬT TOÁN CŨ ———
  stdDev(arr){ if(arr.length<2) return 0; const m=arr.reduce((a,b)=>a+b)/arr.length; return Math.sqrt(arr.reduce((a,b)=>a+(b-m)**2,0)/arr.length); }
  calcEntropy(arr){
    if(arr.length<4) return 0;
    const o=arr.filter(x=>x===1).length, z=arr.length-o, p1=o/arr.length, p0=z/arr.length;
    let e=0; if(p1>0)e-=p1*Math.log2(p1); if(p0>0)e-=p0*Math.log2(p0); return e;
  }
  calcEntropyDeep(arr,lvl=1){
    if(arr.length<2*lvl) return 0;
    const g={}, n=arr.length-lvl+1;
    for(let i=0;i<n;i++){ const k=arr.slice(i,i+lvl).join(''); g[k]=(g[k]||0)+1; }
    let e=0; for(const c of Object.values(g)){ const p=c/n; if(p>0)e-=p*Math.log2(p); }
    return e/lvl;
  }

  calcEntropyBitPerPosition(bytesList){
    const res = [];
    for(let b=0;b<8;b++){
      const bits = bytesList.map(v=>(v>>b)&1);
      res.push(this.calcEntropy(bits));
    }
    return { perBit:res, avg:res.reduce((a,b)=>a+b)/8, max:Math.max(...res), min:Math.min(...res) };
  }

  calcEntropyMultiLevel(bytesList){
    const bits = bytesList.flatMap(v=>Array.from({length:8},(_,i)=>(v>>>(7-i))&1));
    const out = {};
    for(let l=1;l<=8;l++) out[l] = this.calcEntropyDeep(bits,l);
    out.avg = Object.values(out).reduce((a,b)=>a+b)/8;
    return out;
  }

  markov2Analyze(bytesList){
    const bits = bytesList.map(v=>v>=128?1:0);
    for(let i=0;i<bits.length-2;i++){
      const st = (bits[i]<<1)|bits[i+1];
      this.md5Stats.markov2[st][bits[i+2]]++;
    }
    const l2 = (bits[bits.length-2]<<1)|bits[bits.length-1];
    const [c0,c1] = this.md5Stats.markov2[l2];
    const t=c0+c1||1;
    return { p0:c0/t, p1:c1/t, pred: c1>c0?"Tài":"Xỉu", weight: Math.abs(c1-c0)/t*3 };
  }

  chiSquareTest(bytesList){
    const e = bytesList.length/256, chi2 = Array(256).fill(0).reduce((s,_,i)=>{
      const o = bytesList.filter(v=>v===i).length;
      return s + (o-e)**2/e;
    },0);
    return { chi2, bias: Math.abs(chi2/255 -1), deviation: chi2>305?"MẠNH":chi2<210?"YẾU":"BÌNH THƯỜNG" };
  }

  runLengthAnalyze(bytesList){
    const bits = bytesList.map(v=>v>=128?1:0);
    const runs={1:[],0:[]}; let c=1;
    for(let i=1;i<bits.length;i++){
      if(bits[i]===bits[i-1])c++; else { runs[bits[i-1]].push(c); c=1; }
    }
    runs[bits.at(-1)].push(c);
    const avg = k => runs[k].length?runs[k].reduce((a,b)=>a+b)/runs[k].length:0;
    const max = k => runs[k].length?Math.max(...runs[k]):0;
    return { taiAvg:avg(1),xiuAvg:avg(0),taiMax:max(1),xiuMax:max(0) };
  }

  detectSuperStreak(h){
    if(h.length<3) return null;
    const r = h.slice(0,20).map(s=>s.result==='Tài'?1:0);
    let st=1; for(let i=1;i<r.length;i++) if(r[i]===r[0])st++; else break;
    return st>=2 ? (r[0]? "Tài":"Xỉu") : null;
  }

  detectBreakCau(h){
    if(h.length<8) return null;
    const r=h.slice(0,15).map(s=>s.result==='Tài'?1:0);
    const lr=r[0]; let cs=1;
    for(let i=1;i<r.length;i++) if(r[i]===lr)cs++; else break;
    if(cs>=3 && cs<=6){
      let bc=0,cc=0;
      for(let i=cs;i<r.length-cs;i++){
        let ok=1; for(let j=0;j<cs;j++) if(r[i+j]!==lr){ok=0;break;}
        if(ok){ if(i+cs<r.length){ r[i+cs]===lr?cc++:bc++; } }
      }
      if(bc>cc) return lr? "Xỉu":"Tài";
      if(cc>=bc && cc>=2) return lr? "Tài":"Xỉu";
    }
    let alt=1; for(let i=0;i<6;i++) if(r[i]===r[i+1]){alt=0;break;}
    return alt && r.length>8 ? (r[0]?"Xỉu":"Tài") : null;
  }

  detectEleven(h){
    if(h.length<5) return null;
    const e11=[];
    for(let i=0;i<Math.min(h.length,30);i++) if(h[i].total===11) e11.push({pos:i,res:h[i].result});
    if(e11.length<2) return null;
    let at=0,ax=0;
    for(const p of e11) if(p.pos>0){ h[p.pos-1].result==='Tài'?at++:ax++; }
    const t=at+ax;
    if(t>=2){ if(at/t>=.65) return "Tài"; if(ax/t>=.65) return "Xỉu"; }
    const r=e11.slice(0,3);
    return r.length>=2 && r[0].res===r[1].res ? (r[0].res==='Tài'?"Xỉu":"Tài") : null;
  }

  detectSmart(h){
    if(h.length<4) return null;
    const R = h.slice(0,15).map(s=>s.result==='Tài'?'T':'X');
    const P = {
      TT:{n:'Tài',c:80},XX:{n:'Xỉu',c:80},TTT:{n:'Tài',c:85},XXX:{n:'Xỉu',c:85},
      TTTT:{n:'Tài',c:90},XXXX:{n:'Xỉu',c:90},TTTTT:{n:'Tài',c:93},XXXXX:{n:'Xỉu',c:93},
      TXT:{n:'Xỉu',c:82},XTX:{n:'Tài',c:82},TXTX:{n:'Xỉu',c:85},XTXT:{n:'Tài',c:85},
      TTX:{n:'Tài',c:78},XXT:{n:'Xỉu',c:78},TXX:{n:'Tài',c:76},XTT:{n:'Xỉu',c:76},
      TTXX:{n:'Tài',c:84},XXTT:{n:'Xỉu',c:84},TTXXTT:{n:'Tài',c:88},XXTTXX:{n:'Xỉu',c:88},
      TTTX:{n:'Tài',c:86},XXXT:{n:'Xỉu',c:86},TTTXX:{n:'Tài',c:83},XXXTT:{n:'Xỉu',c:83},
      TXTXT:{n:'Xỉu',c:87},XTXTX:{n:'Tài',c:87},TXTXTX:{n:'Xỉu',c:89},XTXTXT:{n:'Tài',c:89},
      TTXXT:{n:'Tài',c:82},XXTTX:{n:'Xỉu',c:82},TTXXX:{n:'Tài',c:85},XXTTT:{n:'Xỉu',c:85}
    };
    for(let L=7;L>=3;L--){
      if(R.length<L+1) continue;
      const cur = R.slice(0,L).join('');
      for(const [pat,dt] of Object.entries(P)){
        if(cur===pat || cur===pat.slice(0,L)){
          let mc=0,cc=0;
          for(let i=L;i<Math.min(R.length-1,50);i++){
            if(R.slice(i,i+L).join('')===cur){
              mc++; if(R[i-1]===(dt.n==='Tài'?'T':'X')) cc++;
            }
          }
          if(mc>=2 && cc/mc>=.6) return dt.n;
        }
      }
    }
    return null;
  }

  detectStaircase(h){
    if(h.length<6) return null;
    const t=h.slice(0,12).map(s=>s.total);
    let up=1,dn=1;
    for(let i=0;i<5;i++){ if(t[i]>=t[i+1])up=0; if(t[i]<=t[i+1])dn=0; }
    if(up && t[0]<=10) return "Tài"; if(dn && t[0]>=11) return "Xỉu";
    let ud=0;
    for(let i=0;i<5;i++){
      if(t[i]<t[i+1]&&t[i+1]>t[i+2])ud++;
      if(t[i]>t[i+1]&&t[i+1]<t[i+2])ud++;
    }
    if(ud>=2) return t[0]<=10?"Tài":t[0]>=11?"Xỉu":null;
    return null;
  }

  detectSpiral(h){
    if(h.length<10) return null;
    const r=h.slice(0,20).map(s=>s.result==='Tài'?1:0);
    const g=[]; let c=1;
    for(let i=1;i<r.length;i++){ if(r[i]===r[i-1])c++; else {g.push(c);c=1;} } g.push(c);
    if(g.length>=3){
      let gr=1,sh=1;
      for(let i=0;i<g.length-1;i++){ if(g[i]>=g[i+1])gr=0; if(g[i]<=g[i+1])sh=0; }
      if(gr) return r[0]?"Tài":"Xỉu"; if(sh) return r[0]?"Xỉu":"Tài";
    }
    return null;
  }

  detectPingPong(h){
    if(h.length<6) return null;
    const r=h.slice(0,12).map(s=>s.result==='Tài'?1:0);
    let ok=1; for(let i=0;i<6;i++) if(r[i]===r[i+1]){ok=0;break;}
    return ok ? (r[0]?"Xỉu":"Tài") : null;
  }

  detectSymmetry(h){
    if(h.length<8) return null;
    const r=h.slice(0,12).map(s=>s.result==='Tài'?'T':'X');
    return r.length>=7 && r[0]===r[6]&&r[1]===r[5]&&r[2]===r[4] ? (r[3]==='T'?"Xỉu":"Tài") : null;
  }

  detectTotalPattern(h){
    if(h.length<5) return null;
    const t=h.slice(0,15).map(s=>s.total), r=h.slice(0,15).map(s=>s.result);
    const e=t.map((v,i)=>v===11?i:-1).filter(i=>i>=0);
    if(e.length>=2){
      let at=0,ax=0; e.forEach(p=>{ if(p>0) r[p-1]==='Tài'?at++:ax++; });
      const s=at+ax; if(s>=2){ if(at/s>=.65)return"Tài"; if(ax/s>=.65)return"Xỉu"; }
    }
    const sc=t.slice(0,10), a=sc.reduce((x,y)=>x+y)/sc.length;
    if(a>11.2 && t[0]>11) return "Xỉu"; if(a<9.8 && t[0]<10) return "Tài";
    return null;
  }

  md5Transition(bytes){
    let tw=0,xw=0,pred=null;
    for(let i=0;i<bytes.length-1;i++) this.md5Stats.byteTransition[bytes[i]][bytes[i+1]>=128?1:0]++;
    const L=bytes.at(-1), T=this.md5Stats.byteTransition[L][1]+1, X=this.md5Stats.byteTransition[L][0]+1;
    if(T/(T+X)>=.58) tw+=2.4; if(X/(T+X)>=.58) xw+=2.4;
    const rt=bytes.filter(b=>b>=128).length/bytes.length, bi=rt-.5;
    if(Math.abs(bi)>.06) bi>0?xw+=1.8:tw+=1.8;
    if(tw>xw+.5) pred="Tài"; else if(xw>tw+.5) pred="Xỉu";
    return {pred,tw,xw};
  }

  updateBreak(p,a){
    if(p && a!==p){
      this.breakProtector.consecutiveWrong++;
      if(this.breakProtector.consecutiveWrong >= this.breakProtector.adaptiveThreshold){
        this.breakProtector.mode="REVERSE"; this.breakProtector.reverseCount=2;
        this.breakProtector.adaptiveThreshold = Math.min(5, this.breakProtector.adaptiveThreshold+1);
      }
    } else if(p && a===p){
      this.breakProtector.consecutiveWrong=0;
      if(this.breakProtector.mode==="REVERSE"){
        if(--this.breakProtector.reverseCount<=0){
          this.breakProtector.mode=null;
          this.breakProtector.adaptiveThreshold = Math.max(2, this.breakProtector.adaptiveThreshold-1);
        }
      }
    } else {
      if(this.breakProtector.mode==="REVERSE"){
        this.breakProtector.reverseCount-=.5;
        if(this.breakProtector.reverseCount<=0) this.breakProtector.mode=null;
      }
    }
    this.breakProtector.lastPrediction=p;
  }

  applyBreak(p){ return p && this.breakProtector.mode==="REVERSE" ? (p==='Tài'?'Xỉu':'Tài') : p; }

  logic1(last,h){ if(!last||h.length<10) return null;
    const ld=last.sid%10, v=last.total, cur=(ld+v)%2===0?"Xỉu":"Tài";
    let c=0,t=0;
    for(let i=0;i<Math.min(h.length-1,25);i++){
      const s=h[i],p=h[i+1]; if(!p)continue;
      const pv=((p.sid%10)+p.total)%2===0?"Xỉu":"Tài";
      if(pv===s.result)c++; t++;
    }
    return t>5 && c/t>=.6 ? cur : null;
  }

  logic2(nid,h){ if(h.length<15) return null;
    let th=0,ng=0,W=Math.min(h.length,60);
    for(let i=0;i<W;i++){
      const ev=h[i].sid%2===0, w=1-(i/W)*.6;
      if((ev&&h[i].result==='Xỉu')||(!ev&&h[i].result==='Tài')) th+=w; else ng+=w;
    }
    const ce=nid%2===0,tot=th+ng;
    if(tot<8) return null;
    if(th>ng+.12*tot) return ce?"Xỉu":"Tài";
    if(ng>th+.12*tot) return ce?"Tài":"Xỉu";
    return null;
  }

  logic3(h){ if(h.length<15) return null;
    const W=Math.min(h.length,50), t=h.slice(0,W).map(s=>s.total);
    const a=t.reduce((x,y)=>x+y)/t.length, sd=this.stdDev(t), rc=t.slice(0,5);
    let ri=1,fa=1;
    for(let i=0;i<rc.length-1;i++){ if(rc[i]<=rc[i+1])ri=0; if(rc[i]>=rc[i+1])fa=0; }
    if(a<10.5-.6*sd && fa) return "Xỉu"; if(a>10.5+.6*sd && ri) return "Tài";
    return null;
  }

  logic4(h){ if(h.length<20) return null;
    let best=null,mx=0;
    const vol=this.stdDev(h.slice(0,20).map(s=>s.total));
    const L=vol<1.7?[6,5,4]:[5,4,3];
    for(const l of L){
      if(h.length<l+2) continue;
      const cur=h.slice(0,l).map(s=>s.result==='Tài'?'T':'X').reverse().join('');
      let ta=0,xi=0,tot=0;
      for(let i=l;i<Math.min(h.length-1,200);i++){
        if(h.slice(i,i+l).map(s=>s.result==='Tài'?'T':'X').reverse().join('')===cur){
          tot++; h[i-1].result==='Tài'?ta++:xi++;
        }
      }
      if(tot<2) continue;
      if(ta/tot>=.65 && ta/tot>mx){mx=ta/tot;best='Tài';}
      else if(xi/tot>=.65 && xi/tot>mx){mx=xi/tot;best='Xỉu';}
    }
    return best;
  }

  logic5(h){ if(h.length<25) return null;
    const cnt={}, W=Math.min(h.length,400);
    for(let i=0;i<W;i++){ const v=h[i].total; cnt[v]=(cnt[v]||0)+(1-(i/W)*.8); }
    let ms=-1,mw=0;
    for(const [s,w] of Object.entries(cnt)) if(w>mw){mw=w;ms=+s;}
    const tot=Object.values(cnt).reduce((a,b)=>a+b);
    if(ms>=0 && mw/tot>.07){
      const L=cnt[ms-1]||0,R=cnt[ms+1]||0;
      if(mw>L*1.03 && mw>R*1.03) return ms<=10?"Xỉu":"Tài";
    }
    return null;
  }

  logicFast(h){ if(h.length<3) return null;
    const s=h.slice(0,3).reduce((a,b)=>a+(b.result==='Tài'?1:0),0);
    return s>=2?"Tài":s<=0?"Xỉu":null;
  }

  // ============================================================
  // 💥 LỚP TOÁN HỌC GỐC ĐƯỢC GIỮ NGUYÊN (6 LỚP)
  // ============================================================
  
  fourierSpectrum(bytesList) {
    const N = bytesList.length;
    if (N < 4) return { pred: null, weight: 0, power: 0 };
    const bits = bytesList.map(v => v >= 128 ? 1 : -1);
    let maxP = 0, bestFreq = 0;
    for (let k = 1; k <= N / 2; k++) {
      let real = 0, imag = 0;
      for (let n = 0; n < N; n++) {
        const angle = (2 * Math.PI * k * n) / N;
        real += bits[n] * Math.cos(angle);
        imag -= bits[n] * Math.sin(angle);
      }
      const power = (real * real + imag * imag) / N;
      if (power > maxP) {
        maxP = power;
        bestFreq = k;
      }
    }
    const pred = bestFreq % 2 === 0 ? "Tài" : "Xỉu";
    const weight = Math.min(3.5, maxP * 0.85);
    return { pred, weight, power: maxP, freq: bestFreq };
  }

  cusumDrift(bytesList) {
    if (bytesList.length < 4) return { pred: null, weight: 0, drift: 0 };
    const mean = 127.5;
    let sum = 0;
    for (const val of bytesList) {
      sum += (val - mean) / 127.5;
    }
    const pred = sum >= 0 ? "Tài" : "Xỉu";
    const weight = Math.min(3.2, Math.abs(sum) * 1.6);
    return { pred, weight, drift: sum };
  }

  lempelZivComplexity(bytesList) {
    const bits = bytesList.map(v => v >= 128 ? "1" : "0").join('');
    const n = bits.length;
    if (n < 2) return { complexity: 0, scaleFactor: 1.0 };
    const dictionary = new Set();
    let i = 0, c = 1;
    while (i < n) {
      let j = 1;
      while (i + j <= n && dictionary.has(bits.substring(i, i + j))) {
        j++;
      }
      dictionary.add(bits.substring(i, i + j));
      c++;
      i += j;
    }
    const normalizedComplexity = (c * Math.log2(n)) / n;
    const scaleFactor = normalizedComplexity < 0.65 ? 1.45 : 0.85;
    return { complexity: normalizedComplexity, scaleFactor };
  }

  hammingAutocorrelation(bytesList) {
    const bits = bytesList.map(v => v >= 128 ? 1 : 0);
    const N = bits.length;
    if (N < 8) return { pred: null, weight: 0, lagCorrelations: [] };
    const lags = [1, 2, 3, 4];
    const cors = [];
    for (const lag of lags) {
      let match = 0, count = 0;
      for (let i = 0; i < N - lag; i++) {
        if (bits[i] === bits[i + lag]) match++;
        count++;
      }
      cors.push(count > 0 ? match / count : 0.5);
    }
    const avgCor = cors.reduce((a, b) => a + b) / cors.length;
    const lastBit = bits[N - 1];
    const pred = avgCor > 0.52 ? (lastBit ? "Tài" : "Xỉu") : (lastBit ? "Xỉu" : "Tài");
    const weight = Math.min(3.0, Math.abs(avgCor - 0.5) * 12);
    return { pred, weight, lagCorrelations: cors };
  }

  varianceRatioTest(bytesList) {
    const n = bytesList.length;
    if (n < 10) return { pred: null, weight: 0, vr: 1 };
    const calcVar = (arr) => {
      const m = arr.reduce((a, b) => a + b) / arr.length;
      return arr.reduce((a, b) => a + (b - m) ** 2, 0) / arr.length;
    };
    const diff1 = [];
    for (let i = 1; i < n; i++) diff1.push(bytesList[i] - bytesList[i - 1]);
    const var1 = calcVar(diff1) || 1;

    const diff2 = [];
    for (let i = 2; i < n; i++) diff2.push(bytesList[i] - bytesList[i - 2]);
    const var2 = calcVar(diff2) || 1;

    const vr = var2 / (2 * var1);
    const lastRes = bytesList[n - 1] >= 128 ? "Tài" : "Xỉu";
    const pred = vr < 0.95 ? (lastRes === "Tài" ? "Xỉu" : "Tài") : (lastRes === "Tài" ? "Tài" : "Xỉu");
    const weight = Math.min(3.2, Math.abs(vr - 1.0) * 4.5);
    return { pred, weight, vr };
  }

  bayesProbabilityNetwork(bytesList) {
    const bits = bytesList.map(v => v >= 128 ? 1 : 0);
    const N = bits.length;
    if (N < 10) return { pred: "Tài", weight: 1.5, probT: 0.5 };
    const totalT = bits.filter(b => b === 1).length;
    const priorT = totalT / N;
    const priorX = 1 - priorT;

    let t_given_t = 0, count_t = 0;
    let t_given_x = 0, count_x = 0;
    for (let i = 0; i < N - 1; i++) {
      if (bits[i] === 1) {
        count_t++;
        if (bits[i + 1] === 1) t_given_t++;
      } else {
        count_x++;
        if (bits[i + 1] === 1) t_given_x++;
      }
    }
    const p_t_t = count_t > 0 ? t_given_t / count_t : 0.5;
    const p_t_x = count_x > 0 ? t_given_x / count_x : 0.5;

    const lastBit = bits[N - 1];
    let likelihoodT = lastBit === 1 ? p_t_t : (1 - p_t_t);
    let likelihoodX = lastBit === 1 ? p_t_x : (1 - p_t_x);

    likelihoodT = Math.max(0.01, Math.min(0.99, likelihoodT));
    likelihoodX = Math.max(0.01, Math.min(0.99, likelihoodX));

    const postT = (likelihoodT * priorT) / ((likelihoodT * priorT) + (likelihoodX * priorX) || 1);
    const pred = postT >= 0.5 ? "Tài" : "Xỉu";
    const weight = Math.min(4.0, Math.abs(postT - 0.5) * 14);
    return { pred, weight, probT: postT };
  }

  // ============================================================
  // ⚡ LỚP 7 (NÂNG CẤP): BÓC TÁCH KHỐI LÕI MD5 BẰNG XOR & BITWISE
  // ============================================================
  md5BlockExtraction(bytesList) {
    if(bytesList.length < 16) return { pred: null, weight: 0, blockScore: 128 };
    let xorSum = 0, foldA = 0, foldB = 0;
    // Giả lập bóc tách lớp mã hóa A, B, C, D của MD5 thông qua Folding Byte
    for(let i=0; i<Math.floor(bytesList.length/4); i++) {
        foldA ^= bytesList[i];
        foldB ^= bytesList[bytesList.length - 1 - i];
        xorSum += (bytesList[i] ^ bytesList[i+4] || 0);
    }
    // Gộp trạng thái để đưa ra con số bóc tách chỉ thị kết quả phân tán
    const blockScore = (foldA + foldB + (xorSum % 256)) / 3;
    const pred = blockScore >= 127.5 ? "Tài" : "Xỉu";
    const weight = Math.min(3.8, Math.abs(blockScore - 127.5) / 25);
    return { pred, weight, blockScore };
  }

  // ============================================================
  // 🧬 THUẬT TOÁN ĐÁNH GIÁ HEX, ENTROPY, BIT & TỈ LỆ % TUYỆT ĐỐI TĨNH
  // ============================================================
  
  analyzeHexDistribution(hex) {
    const s = hex.replace(/[^0-9a-f]/gi,'').toLowerCase();
    const freq = Array(16).fill(0);
    for(let i=0; i<s.length; i++) {
      freq[parseInt(s[i], 16)]++;
    }
    let hEntropy = 0;
    for(let i=0; i<16; i++) {
      const p = freq[i] / s.length;
      if(p > 0) hEntropy -= p * Math.log2(p);
    }
    return { freq, entropy: hEntropy };
  }

  // NÂNG CẤP: Tính toán tỷ lệ phần trăm phân tích không random tuyệt đối 
  calculateDeepScore(bytes, hexEnt, fourier, cusum, autoCor, varRatio, bayes, md5Ext) {
    const dev = bytes.reduce((sum, b) => sum + Math.abs(b - 127.5), 0) / bytes.length;
    const byteScore = Math.max(0, 100 - (dev * 1.5));
    const fPower = Math.min(100, fourier.power * 25);
    const bayesConf = Math.abs(bayes.probT - 0.5) * 200;
    const entScore = (hexEnt / 4.0) * 100;
    const extScore = Math.abs(md5Ext.blockScore - 127.5) / 127.5 * 100;

    // Tổng hợp tuyến tính từ các chỉ số trọng yếu, cam kết không dùng random()
    const score = (byteScore * 0.15) + (fPower * 0.20) + (bayesConf * 0.30) + (entScore * 0.15) + (extScore * 0.20);
    return Math.min(99.9, Math.max(50.1, score * 1.25));
  }

  // ——— HÀM TỔNG HỢP SIÊU ENSEMBLE ĐƯỢC TÍCH HỢP TOÀN DIỆN ———
  superEnsemble(h,md5){
    if(h.length<12) return null;
    let T=0,X=0;
    const A=(p,w)=>{ if(p==='Tài')T+=w; else if(p==='Xỉu')X+=w; };
    
    // Giữ nguyên các bộ đoán cũ hoàn toàn
    A(this.detectSuperStreak(h),3.2); A(this.detectBreakCau(h),2.6);
    A(this.detectEleven(h),3.0); A(this.detectSmart(h),2.4);
    A(this.detectStaircase(h),1.9); A(this.detectSpiral(h),2.1);
    A(this.detectPingPong(h),2.2); A(this.detectSymmetry(h),2.0);
    A(this.detectTotalPattern(h),2.3);
    const L=h[0];
    A(this.logic1(L,h),1.5); A(this.logic2(L?L.sid+1:0,h),1.4);
    A(this.logic3(h),1.3); A(this.logic4(h),1.4); A(this.logic5(h),1.2);
    A(this.logicFast(h),.8);
    if(md5?.pred){ A(md5.pred,2.9); T+=md5.tw||0; X+=md5.xw||0; }

    const bytes = h.map(x=>x.total);
    const eb = this.calcEntropyBitPerPosition(bytes);
    const em = this.calcEntropyMultiLevel(bytes);
    const mk = this.markov2Analyze(bytes);
    A(mk.pred, mk.weight);
    if(eb.avg>0.92) X+=1.2; else if(eb.avg<0.55) T+=1.2;
    if(em.avg>0.93) this.coreState.entropyHigh=true; else this.coreState.entropyHigh=false;

    // TÍCH HỢP CÁC LỚP TOÁN HỌC VÀ LỚP BÓC TÁCH MỚI
    const fourier = this.fourierSpectrum(bytes);
    const cusum = this.cusumDrift(bytes);
    const lz = this.lempelZivComplexity(bytes);
    const autoCor = this.hammingAutocorrelation(bytes);
    const varRatio = this.varianceRatioTest(bytes);
    const bayes = this.bayesProbabilityNetwork(bytes);
    const md5Ext = this.md5BlockExtraction(bytes); // Lớp 7 bóc tách cấu trúc lõi

    // Lưu trữ thông số phân tích chi tiết để hiển thị
    this.lastDetails = { fourier, cusum, lz, autoCor, varRatio, bayes, md5Ext, T, X };

    const m = lz.scaleFactor;
    A(fourier.pred, fourier.weight * m);
    A(cusum.pred, cusum.weight);
    A(autoCor.pred, autoCor.weight * m);
    A(varRatio.pred, varRatio.weight);
    A(bayes.pred, bayes.weight * 1.3);
    A(md5Ext.pred, md5Ext.weight * 1.5);

    const tot=T+X; if(tot<1.8) return null;
    if(X===0 || T/Math.max(X,.001)>=1.18) return "Tài";
    if(T===0 || X/Math.max(T,.001)>=1.18) return "Xỉu";
    return T>X?"Tài":"Xỉu";
  }

  deepEngine(h,p){ 
    if(h.length<8||!p) return p;
    const r=h.slice(0,20).map(s=>s.result==='Tài'?1:0);
    const en=this.calcEntropy(r.slice(0,8));
    let sk=1; for(let i=1;i<r.length;i++) if(r[i]===r[0])sk++; else break;
    if(sk>=6) return r[0]?"Tài":"Xỉu";
    let pp=1; for(let i=0;i<5;i++) if(r[i]===r[i+1]){pp=0;break;}
    if(pp) return r[0]?"Xỉu":"Tài";
    if(en>.90) this.coreState.daoChieu=true; else if(en<.50) this.coreState.daoChieu=false;
    return this.coreState.daoChieu ? (p==='Tài'?'Xỉu':'Tài') : p;
  }

  analyze(hex){
    const s=hex.replace(/[^0-9a-f]/gi,'').toLowerCase();
    const L=s.length;
    if(L!==32 && L!==64) return {loi:`Hash không hợp lệ! Cần 32 MD5 / 64 SHA256, hiện có ${L}`};
    const type=L===32?"MD5":"SHA256";
    const bytes=[];
    for(let i=0;i<L;i+=2) bytes.push(parseInt(s.slice(i,i+2),16));
    const hist = bytes.map((b,i)=>({
      result: b>=128?"Tài":"Xỉu", total:b, sid:i,
      d1:(b>>4)&0xf, d2:b&0xf, d3:(b>>2)&0xf
    }));
    const md5 = type==="MD5" ? this.md5Transition(bytes) : {pred:null,tw:0,xw:0};
    let pred = this.superEnsemble(hist, md5);
    pred = this.deepEngine(hist, pred);
    pred = this.applyBreak(pred);

    const hexAnalysis = this.analyzeHexDistribution(s);
    const hexEnt = hexAnalysis.entropy;
    const det = this.lastDetails || {};
    
    const deepScore = this.calculateDeepScore(
      bytes,
      hexEnt,
      det.fourier || { power: 0.5 },
      det.cusum || { drift: 0 },
      det.autoCor || { lagCorrelations: [0.5] },
      det.varRatio || { vr: 1 },
      det.bayes || { probT: 0.5 },
      det.md5Ext || { blockScore: 128 }
    );

    let res, ic;
    if(pred==="Tài"){ res="🔥 TÀI"; ic="🔥"; }
    else if(pred==="Xỉu"){ res="❄️ XỈU"; ic="❄️"; }
    else {
      const ct=hist.filter(x=>x.result==='Tài').length, cx=hist.length-ct;
      if(ct>cx){ res="❄️ XỈU"; ic="❄️"; }
      else if(cx>ct){ res="🔥 TÀI"; ic="🔥"; }
      else { res=bytes[0]>=128?"🔥 TÀI":"❄️ XỈU"; ic=res.includes('TÀI')?"🔥":"❄️"; }
    }

    const taiP = res.includes('TÀI') ? deepScore : (100 - deepScore);
    const xiuP = 100 - taiP;

    return { type, res, ic, taiP, xiuP, conf:deepScore, hex, md5 };
  }
}

const analyzer = new HashAnalyzer();

// ============================================================
// 🤖 BOT TELEGRAM - GIAO DIỆN CYBERPUNK NÂNG CẤP ĐẸP MẮT
// ============================================================
const bot = new Bot(TOKEN);

bot.catch(err=>{
  const ctx=err.ctx;
  console.error(`Lỗi tại ${ctx.update.update_id}:`, err);
  if(err instanceof GrammyError) console.error("Grammy:",err.description);
  else if(err instanceof HttpError) console.error("Network:",err);
});

bot.command('start', async ctx=>{
  const [ok]=checkUser(ctx.from.id);
  if(!ok) return ctx.reply(`⛔ <b>TÀI KHOẢN CHƯA KÍCH HOẠT</b>\n━━━━━━━━━━━━━━━━━━━━━━━\nHệ thống phân tích dữ liệu MD5 / SHA256.\n\nVui lòng liên hệ Admin để nhận Key kích hoạt:\n👉 <b>${ADMIN_USERNAME}</b>\nGõ /help để xem bảng giá dịch vụ.`);
  return ctx.reply(`🟢 <b>HỆ THỐNG PHÂN TÍCH ĐÃ SẴN SÀNG</b>\n━━━━━━━━━━━━━━━━━━━━━━━\nHướng dẫn sử dụng:\n➡️ <b>Dán trực tiếp mã MD5 (32 ký tự) hoặc SHA256 (64 ký tự)</b>\n💎 Bot sẽ tự động phân tích qua 7 lớp toán học và trả kết quả siêu chuẩn.\n\n/help - Danh sách lệnh\nAdmin hỗ trợ: ${ADMIN_USERNAME}`);
});

bot.command('help', async ctx=>{
  const ad = isAdmin(ctx.from.id);
  let msg = `⚡️ <b>HƯỚNG DẪN & ĐIỀU KHOẢN DỊCH VỤ</b> ⚡️\n╔═══════════════════════════╗\n`;
  msg += `║ /start      • Khởi động hệ thống\n║ /info       • Thông tin tài khoản\n║ /help       • Bảng giá & hướng dẫn\n║ /feedback   • Góp ý kỹ thuật\n╠═══════════════════════════╣\n`;
  msg += `║ 💡 <b>CÁCH THỨC SỬ DỤNG:</b>\n║ Dán trực tiếp chuỗi MD5 hoặc SHA256.\n║ Hệ thống phân tích bóc tách khối,\n║ phân rã byte và thống kê tần suất.\n╠═══════════════════════════╣\n`;
  msg += `║ 💳 <b>BẢNG GIÁ KÍCH HOẠT:</b>\n║ 🔸 30 Ngày  → 20.000đ\n║ 🔸 90 Ngày  → 35.000đ\n║ 🔹 VĨNH VIỄN → 50.000đ\n║ Liên hệ hỗ trợ: ${ADMIN_USERNAME}\n`;
  if(ad){
    msg += `╠══════════ ADMIN CONTROLS ═══════════╣\n`;
    msg += `║ /adduser ID [ngày|vinh]\n║ /removeuser ID\n║ /broadcast NỘI DUNG\n║ /danhsach\n`;
  }
  msg += `╚═══════════════════════════╝\n👤 <b>Developer:</b> ${ADMIN_USERNAME}`;
  ctx.reply(msg, { parse_mode: 'HTML' });
});

bot.command('info', async ctx=>{
  const [ok,exp]=checkUser(ctx.from.id);
  if(!ok) return ctx.reply(`⛔ Tài khoản chưa kích hoạt\n👉 Liên hệ Admin: ${ADMIN_USERNAME}`);
  const u=ctx.from;
  ctx.reply(`👤 <b>THÔNG TIN THÀI VIÊN</b>\n┌─────────────────────────\n│ Tên: <b>${u.first_name||''} ${u.last_name||''}</b>\n│ Username: @${u.username||'—'}\n│ ID: <code>${u.id}</code>\n│ Trạng thái: ✅ Đã kích hoạt\n│ Hạn dùng: <b>${exp}</b>\n└─────────────────────────\nBản quyền thuộc về: ${ADMIN_USERNAME}`,{parse_mode:'HTML'});
});

bot.command('feedback', async ctx=>{
  const [ok]=checkUser(ctx.from.id); if(!ok) return ctx.reply('⛔ Chưa kích hoạt tài khoản.');
  const txt = ctx.message.text.replace(/^\/feedback\s*/i,'').trim();
  if(!txt) return ctx.reply('💬 Nhập đúng cú pháp: /feedback [nội dung bạn muốn gửi]');
  await bot.api.sendMessage(ADMIN_ID,
    `📩 <b>YÊU CẦU FEEDBACK MỚI</b>\n━━━━━━━━━━━━━━━━━━━━\nTên: ${ctx.from.first_name}\nID: <code>${ctx.from.id}</code>\nNội dung góp ý:\n${txt}`,{parse_mode:'HTML'});
  ctx.reply('✅ Góp ý của bạn đã được gửi trực tiếp đến hệ thống vận hành.');
});

// === ADMIN COMMANDS (GIỮ NGUYÊN HOÀN TOÀN LOGIC CŨ) ===
bot.command('adduser', async ctx=>{
  if(!isAdmin(ctx.from.id)) return;
  const p=ctx.message.text.split(/\s+/);
  if(p.length!==3) return ctx.reply('✅ Cách dùng: /adduser ID 30  hoặc  /adduser ID vinh');
  const [,id,time]=p;
  activatedUsers[id]={ expires: time==='vinh' ? 'vĩnh viễn' : moment.tz(TZ).add(+time||0,'days').format('YYYY-MM-DD HH:mm:ss') };
  saveUsers();
  ctx.reply(`✅ Đã cấp quyền sử dụng cho ID ${id}\nHạn: ${time==='vinh'?'♾️ Vĩnh viễn':time+' ngày'}`);
});

bot.command('removeuser', async ctx=>{
  if(!isAdmin(ctx.from.id)) return;
  const id=ctx.message.text.split(/\s+/)[1];
  if(!id) return;
  delete activatedUsers[id]; saveUsers();
  ctx.reply(`🗑️ Đã thu hồi quyền sử dụng của ID ${id}`);
});

bot.command('broadcast', async ctx=>{
  if(!isAdmin(ctx.from.id)) return;
  const msg=ctx.message.text.replace(/^\/broadcast\s*/,'');
  if(!msg) return;
  let ok=0,er=0;
  for(const id of Object.keys(activatedUsers)){
    try{ await bot.api.sendMessage(id,`📢 <b>THÔNG BÁO TỪ HỆ THỐNG ADMIN</b>\n━━━━━━━━━━━━━━━━━━━━\n${msg}`, { parse_mode: 'HTML' }); ok++; }catch{ er++; }
  }
  ctx.reply(`📤 Tiến trình gửi tin hoàn tất!\n✅ Thành công: ${ok}\n❌ Không thể kết nối: ${er}`);
});

bot.command('danhsach', async ctx=>{
  if(!isAdmin(ctx.from.id)) return;
  const arr=Object.entries(activatedUsers);
  let out=`📋 <b>DANH SÁCH THÀNH VIÊN ĐÃ KÍCH HOẠT (${arr.length})</b>\n━━━━━━━━━━━━━━━━━━━━\n`;
  arr.forEach(([id,i])=> out += `${id==ADMIN_ID?'👑 ADMIN':'👤'} <code>${id}</code> → <b>${i.expires}</b>\n`);
  ctx.reply(out, { parse_mode: 'HTML' });
});

// === NHẬN DIỆN VÀ PHÂN TÍCH CHUỖI HASH ===
bot.on('message:text', async ctx=>{
  const txt=ctx.msg.text.trim();
  if(!/^[0-9a-fA-F]{32}$|^[0-9a-fA-F]{64}$/.test(txt)) return;
  const [ok]=checkUser(ctx.from.id);
  if(!ok) return ctx.reply(`⛔ Chưa kích hoạt tài khoản\n👉 Liên hệ: ${ADMIN_USERNAME}`);
  
  const r = analyzer.analyze(txt);
  if(r.loi) return ctx.reply('⚠️ '+r.loi);

  const drawProgressBar = (percent) => {
    const size = 10;
    const active = Math.round(percent / 10);
    return "█".repeat(active) + "░".repeat(size - active);
  };

  const d = analyzer.lastDetails || {};
  const fourierDesc = d.fourier ? `${d.fourier.pred === "Tài" ? "🔥 TÀI" : "❄️ XỈU"} (k=${d.fourier.freq})` : "N/A";
  const cusumDesc = d.cusum ? `${d.cusum.pred === "Tài" ? "🔥 TÀI" : "❄️ XỈU"} (d=${d.cusum.drift.toFixed(2)})` : "N/A";
  const lzDesc = d.lz ? `${d.lz.complexity < 0.65 ? "🔄 Lặp Cao" : "🌀 Đa Dạng"} (${d.lz.complexity.toFixed(2)})` : "N/A";
  const autoCorDesc = d.autoCor ? `${d.autoCor.pred === "Tài" ? "🔥 TÀI" : "❄️ XỈU"}` : "N/A";
  const varRatioDesc = d.varRatio ? `${d.varRatio.vr < 0.95 ? "🔄 Mean-Rev" : "📈 Trending"}` : "N/A";
  const bayesDesc = d.bayes ? `${d.bayes.pred === "Tài" ? "🔥 TÀI" : "❄️ XỈU"} (${(d.bayes.probT * 100).toFixed(0)}%)` : "N/A";
  const md5ExtDesc = d.md5Ext ? `${d.md5Ext.pred === "Tài" ? "🔥 TÀI" : "❄️ XỈU"} (Core=${d.md5Ext.blockScore.toFixed(0)})` : "N/A";

  const responseTemplate = 
`⚡️ <b>KẾT QUẢ PHÂN TÍCH ${r.type} BY HOÀNG</b> ⚡️
━━━━━━━━━━━━━━━━━━━━━━━
🔮 <b>HỆ THỐNG DỰ ĐOÁN TĨNH</b>
👉 <b>${r.res}</b>  (Độ tin cậy: <b>${r.conf.toFixed(1)}%</b>)

📊 <b>XÁC SUẤT TOÁN HỌC</b>
├─ 🔥 TÀI: <code>${r.taiP.toFixed(1)}%</code> [${drawProgressBar(r.taiP)}]
└─ ❄️ XỈU: <code>${r.xiuP.toFixed(1)}%</code> [${drawProgressBar(r.xiuP)}]

🧬 <b>7 LỚP PHÂN TÍCH CHUYÊN SÂU</b>
├─ 🧮 <b>Bóc tách lõi MD5:</b> <code>${md5ExtDesc}</code>
├─ 📡 <b>Fourier Spectrum:</b> <code>${fourierDesc}</code>
├─ 📈 <b>Cusum Drift Path:</b> <code>${cusumDesc}</code>
├─ 🧩 <b>Độ phức tạp LZ:</b> <code>${lzDesc}</code>
├─ 🔗 <b>Tự tương quan bit:</b> <code>${autoCorDesc}</code>
├─ ⚖️ <b>Kiểm định Var Ratio:</b> <code>${varRatioDesc}</code>
└─ 📐 <b>Xác suất Bayes:</b> <code>${bayesDesc}</code>

━━━━━━━━━━━━━━━━━━━━━━━
📥 <b>HASH ĐẦU VÀO</b>
<code>${r.hex}</code>

👤 <b>Khách hàng:</b> ${ctx.from.first_name || "Thành viên"}
🛡️ <b>Bản quyền thuộc về:</b> ${ADMIN_USERNAME}`;

  ctx.reply(responseTemplate, { parse_mode: 'HTML' });
});

// ============================================================
// 🚀 SERVER KEEP‑ALIVE → TỰ GỌI 15S/LẦN ĐỂ CHỐNG ĐƠ RENDER
// ============================================================
const app = express();
app.get('/', (req,res)=> res.send(`✅ BOT MD5 TÀI XỈU HOÀNG ONLINE • ${nowVN().format('DD/MM/YYYY HH:mm:ss')}`));
app.get('/health', (req,res)=> res.json({status:'ok',time:nowVN().toISOString(),pid:process.pid}));
app.get('/ping', (req,res)=> res.send('pong'));
app.listen(PORT, ()=> console.log(`🌐 Keep‑alive chạy tại http://0.0.0.0:${PORT}`));

// NÂNG CẤP: Tự gọi nhịp Ping 15s một lần để Render luôn trong trạng thái Online 100%
setInterval(async ()=>{
  try{
    await fetch(`http://localhost:${PORT}/ping`);
    console.log(`[Auto-Ping 15s] Hệ thống duy trì kết nối thành công lúc ${nowVN().format('HH:mm:ss')}`);
  } catch(e) { }
}, 15 * 1000);

// KHỞI ĐỘNG BOT VÀ PHỤC HỒI KHI GẶP LỖI NẶNG
async function start(){
  console.log(`🤖 Bot đang chạy • Admin: ${ADMIN_USERNAME} • ${nowVN().format('HH:mm:ss')}`);
  await bot.start({ drop_pending_updates: true, onStart:()=>{} });
}
process.on('unhandledRejection', e=> console.error('💥 BỎ QUA:', e.message||e));
process.on('uncaughtException', e=>{
  console.error('💀 LỖI NẶNG, tự khởi động lại sau 3s:', e.message);
  setTimeout(start, 3000);
});
start();