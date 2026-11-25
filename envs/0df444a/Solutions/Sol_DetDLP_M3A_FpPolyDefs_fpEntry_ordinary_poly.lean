-- Prove2me | solution 1 for DetDLP.M3A.FpPolyDefs.fpEntry_ordinary_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T02:24:34.392742+00:00
-- url     : https://prove2.me/submissions/0924b28c-a9f9-4fb9-a4ee-74e0373badad

import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_PolyT_len_mul_le
import Definitions.Def_DetDLP_M3A_FpPolyDefs
set_option autoImplicit false
namespace DetDLP.M3A.FpPolyDefs
set_option maxHeartbeats 800000
attribute [local fun_prop] w4_M5Evaluator.n0_poly w4_M5Evaluator.J_poly w4_M5Evaluator.L1_poly w4_M5Evaluator.L2_poly
open Groundwork S8H.PointAddresses S8L.FpPair.Address w4_MulParams w4_M5GraphBounds
attribute [local fun_prop] PolyT.add PolyT.mul PolyT.div PolyT.mod PolyT.sub PolyT.const PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' P2M_Groundwork_PolyT_ite__226169acf219
private structure PC {α : Type} [Enc α] (a : α → Code) : Prop where
  ng : PolyT fun x => (a x).ng
  nb : PolyT fun x => (a x).nb
  ne : PolyT fun x => (a x).ne
  gate : ∀ {β : Type} [Enc β] {h : β → α} {e : β → ℕ}, PolyT h → PolyT e → PolyT fun x => (a (h x)).gate (e x)
  bit : ∀ {β : Type} [Enc β] {h : β → α} {e : β → ℕ}, PolyT h → PolyT e → PolyT fun x => (a (h x)).bit (e x)
variable {α : Type} [Enc α]
private theorem ofUnif {c : ℕ → Code} {d : α → ℕ} (h : Uniform c) (hd : PolyT d) : PC (fun x => c (d x)) :=
  ⟨h.ng hd,h.nb hd,h.ne hd,fun hh he => h.gate (PolyT.comp hd hh) he,fun hh he => h.bit (PolyT.comp hd hh) he⟩
private theorem pc_sum {a b : α → Code} (h : PC a) (k : PC b) : PC (fun x => sum (a x) (b x)) := by
  constructor
  · exact PolyT.add h.ng k.ng
  · exact PolyT.add h.nb k.nb
  · exact PolyT.add h.ne k.ne
  · intro β _ f e hf he; have hn := PolyT.comp h.ne hf;have hg := PolyT.comp h.ng hf
    exact PolyT.ite' (PolyT.decide_lt he hn) (h.gate hf he) (PolyT.add hg (k.gate hf (PolyT.sub he hn)))
  · intro β _ f e hf he; have hn := PolyT.comp h.ne hf;have hb := PolyT.comp h.nb hf
    exact PolyT.ite' (PolyT.decide_lt he hn) (h.bit hf he) (PolyT.add hb (k.bit hf (PolyT.sub he hn)))
private theorem pc_splice {a : α → Code} {n : α → ℕ} {l r : α → ℕ → ℕ} (h : PC a) (hn : PolyT n) (hl : PolyT fun z : α × ℕ => l z.1 z.2) (hr : PolyT fun z : α × ℕ => r z.1 z.2) : PC (fun x => splice (a x) (n x) (l x) (r x)) := by
  constructor
  · exact PolyT.add h.ng hn
  · exact h.nb
  · exact PolyT.add h.ne (PolyT.add hn hn)
  all_goals intro β _ f e hf he; have ha := PolyT.comp h.ne hf; have hn' := PolyT.comp hn hf; have hg := PolyT.comp h.ng hf; have hu := PolyT.sub he ha; simp only [splice]
  · exact PolyT.ite' (PolyT.decide_lt he ha) (h.gate hf he) (PolyT.add hg (PolyT.ite' (PolyT.decide_lt hu hn') hu (PolyT.sub hu hn')))
  · exact PolyT.ite' (PolyT.decide_lt he ha) (h.bit hf he) (PolyT.ite' (PolyT.decide_lt hu hn') (PolyT.comp hl (PolyT.prodMk hf hu)) (PolyT.comp hr (PolyT.prodMk hf (PolyT.sub hu hn'))))
private theorem pc_repeat {a : α → Code} {n : α → ℕ} (h : PC a) (hn : PolyT n) : PC (fun x => repeatCode (n x) (a x)) := by
  refine ⟨PolyT.mul hn h.ng,PolyT.mul hn h.nb,PolyT.mul hn h.ne,?_,?_⟩
  all_goals intro β _ f e hf he;have hn' := PolyT.comp h.ne hf;have hg := PolyT.comp h.ng hf;have hb := PolyT.comp h.nb hf
  · exact PolyT.add (h.gate hf (PolyT.mod he hn')) (PolyT.mul hg (PolyT.div he hn'))
  · exact PolyT.add (h.bit hf (PolyT.mod he hn')) (PolyT.mul hb (PolyT.div he hn'))
private theorem pc_anchor {k : α → ℕ} (hk : PolyT k) : PC fun x => S8H0.AnchoredLayout.anchorCode (k x) := ⟨hk,hk,hk,fun _ he => he,fun _ he => he⟩
private theorem pc_linked {d : α → ℕ} (hd : PolyT d) : PC (fun x => linked (d x)) := by
  apply pc_splice (ofUnif stage_poly hd) (PolyT.mul (PolyT.const 4) hd)
  all_goals have hh := PolyT.comp hd (PolyT.fst (PolyT.id' (α:=α × ℕ)));have H := mul_poly.nb hh;simp only [addrN,w4_M5EdgeNat.edgeBase,w4_M5GraphBounds.W];fun_prop
private theorem pc_stage {d : α → ℕ} (hd : PolyT d) : PC (fun x => stage (d x)) := by
  apply pc_splice (pc_sum (pc_linked hd) (ofUnif (add_poly (·+1) (by intros;fun_prop)) hd)) hd
  all_goals have hh := PolyT.comp hd (PolyT.fst (PolyT.id' (α:=α × ℕ)));have H := (pc_linked hh).nb;have H' := mul_poly.nb hh;(try simp only [addrN]);fun_prop
private def rawLink (d : ℕ) := splice (stageCode d) (2*d+2*d)
  (fun e => if e<2*d then (mul d).nb+(mul d).nb+(4*e+0) else (mul d).nb+(mul d).nb+(4*(e-2*d)+2))
  (fun e => if e<2*d then (mul d).nb+w4_M5EdgeNat.edgeBase d 9 e else w4_M5EdgeNat.edgeBase d 9 (e-2*d))
private def rawRow (d j l i : ℕ) := (stageCode d).nb+(4*(i+(d+1)*j)+l)
private def rawPhys (d : ℕ) := splice (sum (rawLink d) (add (8*(d+1)))) (3*d+5*(d+1))
  (fun e => if e<3*d then rawRow d (if e/d=0 then 0 else if e/d=1 then 1 else 5) (if e/d<2 then 2 else 0) (e%d)
    else let t := e-3*d;let j := t/(d+1);let i := t%(d+1);rawRow d (if j=0 then 1 else if j=1 then 3 else if j=2 then 4 else if j=3 then 5 else 7) (if j=0 then 2 else if j=3 then 2 else if j=4 then 1 else 0) i)
  (fun e => if e<3*d then (if e/d=0 then e%d else if e/d=1 then d+e%d else (mul d).nb+(mul d).nb+(4*(e%d)+1))
    else let t := e-3*d;let j := t/(d+1);let i := t%(d+1);rawRow d (if j=0 then 2 else if j=2 then 5 else 6) (if j=3 then 2 else if j=4 then 1 else 0) i)
private theorem pc_raw {d : α → ℕ} (hd : PolyT d) : PC (fun x => rawPhys (d x)) := by
  have L : PC (fun x => rawLink (d x)) := by
    apply pc_splice (ofUnif stage_poly hd) (by fun_prop)
    all_goals have hh := PolyT.comp hd (PolyT.fst (PolyT.id' (α:=α × ℕ)));have H := mul_poly.nb hh;(try simp only [w4_M5EdgeNat.edgeBase,w4_M5GraphBounds.W]); fun_prop
  apply pc_splice (pc_sum L (ofUnif (add_poly (fun x => 8*(x+1)) (by intros;fun_prop)) hd)) (by fun_prop)
  all_goals have hh := PolyT.comp hd (PolyT.fst (PolyT.id' (α:=α × ℕ))); have H := mul_poly.nb hh;have H' := stage_poly.nb hh; simp only [rawRow];fun_prop
private theorem pc_slot {d k : α → ℕ} (hd : PolyT d) (hk : PolyT k) : PC (fun x => slot (d x) (k x)) := by
  apply pc_splice (pc_sum (pc_raw hd) (pc_anchor hk)) (hn:=show PolyT (fun x => min (k x) (d x+1)) by simp only [Nat.min_def];fun_prop)
  · have H := stage_poly.nb (PolyT.comp hd (PolyT.fst (PolyT.id' (α:=α × ℕ))));change PolyT fun z : α × ℕ => rawRow (d z.1) 3 0 z.2;unfold rawRow;fun_prop
  · have H := (pc_raw (PolyT.comp hd (PolyT.fst (PolyT.id' (α:=α × ℕ))))).nb;exact PolyT.add H (PolyT.snd PolyT.id')

private theorem pc_base {m d k : α → ℕ} (hm : PolyT m) (hd : PolyT d) (hk : PolyT k) : PC (fun x => base (m x) (d x) (k x)) := by
  let h := pc_repeat (pc_stage hd) (PolyT.mul (PolyT.const 2) hm)
  exact pc_sum (pc_repeat (pc_slot hd hk) (PolyT.mul (PolyT.const 4) hm)) (pc_sum h h)
private theorem pc_chains {m d k : α → ℕ} (hm : PolyT m) (hd : PolyT d) (hk : PolyT k) : PC (fun x => chains (m x) (d x) (k x)) := by
  apply pc_splice (pc_base hm hd hk) (by fun_prop)
  all_goals have hd' := PolyT.comp hd (PolyT.fst (PolyT.id' (α:=α × ℕ)));have hm' := PolyT.comp hm (PolyT.fst (PolyT.id' (α:=α × ℕ)));have hk' := PolyT.comp hk (PolyT.fst (PolyT.id' (α:=α × ℕ)));have H := (pc_slot hd' hk').nb; have U := (pc_linked hd').nb;have V := (pc_stage hd').nb
            simp only [tie,sPort,xPort,Bool.false_eq_true,if_true,if_false];fun_prop
private theorem pc_arith {m d k n : α → ℕ} (hm : PolyT m) (hd : PolyT d) (hk : PolyT k) (hn : PolyT n) : PC (fun x => arith (m x) (d x) (k x) (n x)) := by
  have hmin : PolyT (fun x => min (n x) (4*m x*d x)) := by simp only [Nat.min_def];fun_prop
  apply pc_splice (pc_sum (pc_chains hm hd hk) (pc_anchor (PolyT.add hmin (PolyT.const 1)))) hmin
  · have hd' := PolyT.comp hd (PolyT.fst (PolyT.id' (α:=α × ℕ)));have hm' := PolyT.comp hm (PolyT.fst (PolyT.id' (α:=α × ℕ)));have hk' := PolyT.comp hk (PolyT.fst (PolyT.id' (α:=α × ℕ)));have H := (pc_slot hd' hk').nb; have U := (pc_linked hd').nb; simp only [prefixAddr,xPort];fun_prop
  · have H := PolyT.comp (pc_chains hm hd hk).nb (PolyT.fst (PolyT.id' (α:=α × ℕ)));exact PolyT.add H (PolyT.snd PolyT.id')
private theorem pc_whole {m d k n : α → ℕ} (hm : PolyT m) (hd : PolyT d) (hk : PolyT k) (hn : PolyT n) : PC (fun x => whole (m x) (d x) (k x) (n x)) := by
  let C := pc_arith hm hd hk hn
  refine ⟨PolyT.add C.ng (PolyT.mul (PolyT.const 4) hm), C.nb, PolyT.add C.ne (PolyT.mul (PolyT.mul (PolyT.const 4) hm) hk),?_,?_⟩
  all_goals intro β _ f e hf he; have hd' := PolyT.comp hd hf;have hk' := PolyT.comp hk hf;have H := (pc_slot hd' hk').nb;have U := (pc_linked hd').nb;have hg := PolyT.comp C.ng hf;have hne := PolyT.comp C.ne hf;have hgate := C.gate hf he;have hbit := C.bit hf he
            simp only [whole,M3B.ECLayout.code,zPort];fun_prop

attribute [local fun_prop] PolyT.const PolyT.add PolyT.mul PolyT.sub PolyT.length PolyT.getD PolyT.id' PolyT.comp PolyT.bits PolyT.fst PolyT.snd PolyT.prodMk PolyT.map PolyT.append m89_enum_words.fields_poly w5_M6Sort.decode_poly w5_M6Sort.cw_poly DetDLP_W1_Queries.frame_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f
private theorem uadd {α} [Enc α] {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary (fun x => f x+g x) := by
  apply (PolyT.append hf hg).congr;intro x;rw [List.replicate_add]
private theorem umul {α} [Enc α] {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary (fun x => f x*g x) := by
  have H := PolyT.flatMap (f:=fun x (_ : Unit) => List.replicate (g x) ()) (PolyT.comp hg (PolyT.fst PolyT.id')) hf
  apply H.congr;intro x;change _ = List.replicate (f x*g x) ();generalize f x=n;induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ,List.flatMap_cons,ih,Nat.succ_mul];rw [← List.replicate_add,Nat.add_comm]
private theorem uconst {α} [Enc α] (k : ℕ) : Unary (fun _ : α => k) := PolyT.const _
private theorem sizes (M D K n : ℕ) : let c := whole M D K n; c.ng+c.nb+c.ne+c.ne ≤ 1000000*(M+1)*(D+K+n+1) := by
  intro c
  have H : (mul D).ng ≤ 256*(D+1) ∧ (mul D).nb ≤ 1100*(D+1) := by
    cases D with
    | zero => decide
    | succ D =>
      have hd : 1 ≤ D+1 := by omega
      have h1 := J_lt_linear hd; have h2 := n0_upper hd;have h3 := L_le_half_J hd;have h4 := L1_le_L (D+1);have h5 := L2_le_L (D+1)
      refine ⟨?_,by change wires (D+1) ≤ _;rw [wires_eq hd];exact (graph_edge_bound hd).le⟩
      change vertexCount (D+1) ≤ _;unfold vertexCount;rw [Nat.mul_comm (L2 _) (L1 _),L1_mul_L2];omega
  let u := (mul D).ng;let v := (mul D).nb
  have g : (slot D K).ng = (u+u+2*D+(2*D+2*D)+8*(D+1)+(3*D+5*(D+1))+K+min K (D+1)) := by rfl
  have b : (slot D K).nb = (2*v+2*D*4+8*(D+1)*4+K) := by dsimp [slot,FpSlotTile.slotCode];change v+v+2*D*4+8*(D+1)*4+K=_;ring
  have e : (slot D K).ne = 4*v+2*D*5+2*(2*D+2*D)+8*(D+1)*5+2*(3*D+5*(D+1))+K+2*min K (D+1) := by change v+v+(v+v)+2*D*5+((2*D+2*D)+(2*D+2*D))+8*(D+1)*5+((3*D+5*(D+1))+(3*D+5*(D+1)))+K+(min K (D+1)+min K (D+1))=_;ring
  have hu : u ≤ 256*(D+1) := H.1;have hv : v ≤ 1100*(D+1) := H.2
  have gu : (stage D).ng = u+u+2*D+4*D+(D+1)+D := rfl
  have bu : (stage D).nb = v+v+2*D*4+(D+1)*4 := rfl
  have eu : (stage D).ne = v+v+(v+v)+2*D*5+(4*D+4*D)+(D+1)*5+(D+D) := rfl
  simp only [c,whole,M3B.ECLayout.code,arith,chains,base,splice,sum,repeatCode,S8H0.AnchoredLayout.anchorCode,g,b,e,gu,bu,eu]
  nlinarith only [Nat.mul_le_mul_left M hu,Nat.mul_le_mul_left M hv,Nat.mul_le_mul_left M (min_le_left K (D+1)),min_le_left n (4*M*D)]
attribute [local fun_prop] PolyT.sub PolyT.mul PolyT.div PolyT.mod P2M_Groundwork_PolyT_cons__3a60f43a3b86
private theorem params : PolyT d ∧ PolyT m ∧ PolyT k ∧ PolyT pre ∧ PolyT sizeField ∧ PolyT prec ∧ PolyT len := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | unfold d | unfold m | unfold k | unfold pre | unfold sizeField | unfold prec | unfold len
  all_goals dsimp only [d,m,k,pre,prec,len,width,num,field,nums,fld,prime,threshold,groupSize,dFilt];fun_prop
open Groundwork S8H.PointAddresses S8L.FpPair.Address

attribute [local fun_prop] PolyT.const PolyT.add PolyT.sub PolyT.mul PolyT.mod PolyT.div PolyT.length PolyT.getD PolyT.id' PolyT.comp PolyT.fst PolyT.snd PolyT.prodMk PolyT.map PolyT.append PolyT.filter PolyT.testBit PolyT.all PolyT.idxOf PolyT.zip PolyT.range PolyT.toNat' PolyT.decide_eq PolyT.decide_ne PolyT.ite' PolyT.decide_lt PolyT.decide_le PolyT.decide_and PolyT.and' PolyT.or' PolyT.not' P2M_Groundwork_PolyT_ite__226169acf219 P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_id__1c5d0f44cc8f w4_M5GateOps.portList_poly w4_M5EdgeNat.srcNat_poly w4_M5Dispatch.evalNat_poly
private theorem dpoly {f : α → ℕ} (h : Unary f) : PolyT f := (PolyT.length (PolyT.range h)).congr (by simp)
@[local fun_prop] private theorem eq_poly {a : α → W} (h : PolyT a) : PolyT fun x => equal (a x) := by unfold equal bit;apply PolyT.all _ h;have := PolyT.comp h (PolyT.fst (PolyT.id' (α:=α × Bool)));fun_prop
@[local fun_prop] private theorem decide_imp {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : PolyT fun x => decide (p x)) (hq : PolyT fun x => decide (q x)) : PolyT fun x => decide (p x → q x) := by
  exact (PolyT.or' (PolyT.not' hp) hq).congr fun x => by simp
attribute [local fun_prop] decide_imp
@[local fun_prop] private theorem col_poly {n i : α → ℕ} {c : α → Bool} {a : α → W} (hn : PolyT n) (hi : PolyT i) (hc : PolyT c) (ha : PolyT a) : PolyT fun x => col (n x) (i x) (c x) (a x) := by
  unfold col bit
  have B0 : PolyT (fun x => (a x).getD 0 false) := PolyT.getD ha (PolyT.const 0) (PolyT.const false)
  have B1 : PolyT (fun x => (a x).getD 1 false) := PolyT.getD ha (PolyT.const 1) (PolyT.const false)
  have B2 : PolyT (fun x => (a x).getD 2 false) := PolyT.getD ha (PolyT.const 2) (PolyT.const false)
  have B3 : PolyT (fun x => (a x).getD 3 false) := PolyT.getD ha (PolyT.const 3) (PolyT.const false)
  have B4 : PolyT (fun x => (a x).getD 4 false) := PolyT.getD ha (PolyT.const 4) (PolyT.const false)
  have I : PolyT (fun x => if i x=0 then c x else (a x).getD 4 false) := by fun_prop
  have C0 : PolyT (fun x => (a x).getD 0 false |>.toNat) := PolyT.toNat' B0
  have C1 : PolyT (fun x => (a x).getD 1 false |>.toNat) := PolyT.toNat' B1
  have C2 : PolyT (fun x => (a x).getD 2 false |>.toNat) := PolyT.toNat' B2
  have C3 : PolyT (fun x => (a x).getD 3 false |>.toNat) := PolyT.toNat' B3
  have CI : PolyT (fun x => (if i x=0 then c x else (a x).getD 4 false).toNat) := PolyT.toNat' I
  have E : PolyT (fun x => decide (i x+1=n x)) := PolyT.decide_eq (by fun_prop) hn
  have V : PolyT (fun x => decide ((a x).getD 3 false = false)) := PolyT.decide_eq B3 (PolyT.const false)
  have R : PolyT (fun x => decide (i x+1=n x → (a x).getD 3 false = false)) := by
    exact (PolyT.or' (PolyT.not' E) V).congr fun x => by simp
  have Nlhs : PolyT (fun x => ((a x).getD 0 false).toNat + ((a x).getD 1 false).toNat + (if i x=0 then c x else (a x).getD 4 false).toNat) := by fun_prop
  have Nrhs : PolyT (fun x => ((a x).getD 2 false).toNat + 2 * ((a x).getD 3 false).toNat) := by fun_prop
  have S : PolyT (fun x => decide (((a x).getD 0 false).toNat + ((a x).getD 1 false).toNat + (if i x=0 then c x else (a x).getD 4 false).toNat = ((a x).getD 2 false).toNat + 2 * ((a x).getD 3 false).toNat)) := PolyT.decide_eq Nlhs Nrhs
  exact PolyT.decide_and S R
@[local fun_prop] private theorem rows_poly {d p t g : α → ℕ} {a : α → W} (hd : PolyT d) (hp : PolyT p) (ht : PolyT t) (hg : PolyT g) (ha : PolyT a) : PolyT fun x => rows (d x) (p x) (t x) (g x) (a x) := by
  have hbit (j : ℕ) := PolyT.getD ha (PolyT.const j) (PolyT.const false)
  have hn := PolyT.add hd (PolyT.const 1)
  have hi := PolyT.mod hg hn
  have hj := PolyT.div hg hn
  have hmin := PolyT.ite' (PolyT.decide_le ht hp) ht hp
  unfold rows
  simp only [Nat.min_def]
  apply PolyT.ite' (PolyT.decide_eq hj (PolyT.const 7))
  · refine PolyT.decide_and (PolyT.decide_eq (hbit 0) (hbit 3)) (PolyT.decide_and (PolyT.decide_eq (hbit 2) (PolyT.const false)) (PolyT.decide_and (decide_imp (PolyT.decide_ne hi (PolyT.const 0)) (PolyT.decide_eq (hbit 0) (hbit 4))) (PolyT.decide_eq (hbit 1) (PolyT.and' (hbit 0) (PolyT.testBit hp hi)))))
  · apply PolyT.and' (col_poly hn hi (PolyT.decide_lt hj (PolyT.const 5)) ha)
    apply PolyT.decide_and (decide_imp (PolyT.decide_lt hj (PolyT.const 2)) (PolyT.decide_and (PolyT.decide_eq (hbit 1) (PolyT.const false)) (decide_imp (PolyT.decide_eq hi hd) (PolyT.decide_eq (hbit 2) (PolyT.const false)))))
    apply PolyT.decide_and (decide_imp (PolyT.decide_and (PolyT.decide_eq hj (PolyT.const 0)) (PolyT.decide_eq hi hd)) (PolyT.decide_eq (hbit 0) (PolyT.const false)))
    apply PolyT.decide_and (decide_imp (PolyT.decide_or (PolyT.decide_eq hj (PolyT.const 2)) (PolyT.decide_eq hj (PolyT.const 4))) (PolyT.decide_eq (hbit 2) (PolyT.testBit hp hi)))
    apply PolyT.decide_and (decide_imp (PolyT.decide_eq hj (PolyT.const 3)) (PolyT.decide_eq (hbit 2) (PolyT.testBit hmin hi)))
    exact decide_imp (PolyT.decide_and (PolyT.decide_eq hj (PolyT.const 5)) (PolyT.decide_eq hi hd)) (PolyT.decide_and (PolyT.decide_eq (hbit 0) (PolyT.const false)) (PolyT.decide_eq (hbit 1) (PolyT.const false)))
attribute [local irreducible] w4_M5GateOps.portList S8J.HashGatePoly.mulLayoutCheck
private theorem mulchk {d g : α → ℕ} {a : α → W} (hd : Unary d) (hg : PolyT g) (ha : PolyT a) : PolyT fun x => mulCheck (d x) (g x) (a x) := by
  let ps x := w4_M5GateOps.portList (List.replicate (d x) ()) (g x)
  have hl : PolyT ps := w4_M5GateOps.portList_poly (q:=fun x => List.replicate (d x) ()) (v:=g) hd hg
  have fst := PolyT.fst (PolyT.id' (α:=α × ℕ));have du := PolyT.comp (dpoly hd) fst;have gu := PolyT.comp hg fst
  have first : PolyT (fun z : α × ℕ => d z.1) := PolyT.comp (dpoly hd) (PolyT.fst (PolyT.id' (α:=α × ℕ)))
  have second : PolyT (fun z : α × ℕ => z.2) := PolyT.snd (PolyT.id' (α:=α × ℕ))
  have gate : PolyT (fun z : α × ℕ => g z.1) := PolyT.comp hg (PolyT.fst (PolyT.id' (α:=α × ℕ)))
  have src : PolyT (fun z : α × ℕ => w4_M5EdgeNat.srcNat (d z.1) z.2) := w4_M5EdgeNat.srcNat_poly first second
  have lhs : PolyT (fun z : α × ℕ => w4_M5EdgeNat.srcNat (d z.1) z.2 == g z.1) := PolyT.beq' src gate
  have rhs : PolyT (fun z : α × ℕ => w4_M5EdgeNat.srcNat (d z.1) z.2 != g z.1) := PolyT.bne' src gate
  let ls (x : α) := (ps x).filter (fun e => w4_M5EdgeNat.srcNat (d x) e == g x)
  let rs (x : α) := (ps x).filter (fun e => w4_M5EdgeNat.srcNat (d x) e != g x)
  have hL : PolyT ls := PolyT.filter (l:=ps) (f:=fun x e => w4_M5EdgeNat.srcNat (d x) e == g x) lhs hl
  have hR : PolyT rs := PolyT.filter (l:=ps) (f:=fun x e => w4_M5EdgeNat.srcNat (d x) e != g x) rhs hl
  have pairPorts : PolyT (fun x => ls x ++ rs x) := PolyT.append hL hR
  have pairPorts' : PolyT (fun z : α × ℕ => ls z.1 ++ rs z.1) := PolyT.comp pairPorts (PolyT.fst (PolyT.id' (α:=α × ℕ)))
  have indices : PolyT (fun z : α × ℕ => (ls z.1 ++ rs z.1).idxOf z.2) := PolyT.idxOf (PolyT.snd (PolyT.id' (α:=α × ℕ))) pairPorts'
  have words : PolyT (fun z : α × ℕ => a z.1) := PolyT.comp ha (PolyT.fst (PolyT.id' (α:=α × ℕ)))
  have hbitsFn : PolyT (fun z : α × ℕ => (a z.1).getD ((ls z.1 ++ rs z.1).idxOf z.2) false) := PolyT.getD words indices (PolyT.const false)
  have hbits := PolyT.map (l:=ps) (f:=fun x e => (a x).getD ((ls x ++ rs x).idxOf e) false) hbitsFn hl
  unfold mulCheck
  exact S8J.HashGatePoly.mulLayoutCheck_poly (d:=d) (g:=g) (portBits:=fun x => (ps x).map (fun e => (a x).getD ((ls x ++ rs x).idxOf e) false)) hd hg hbits
private theorem linkedChk {d g : α → ℕ} {a : α → W} (hd : Unary d) (hg : PolyT g) (ha : PolyT a) : PolyT fun x => linkedGate (d x) (g x) (a x) := by
  have h := dpoly hd
  have M := mul_poly.ng h
  have S := stage_poly.ng h
  have A := mulchk hd (PolyT.mod hg M) ha
  have C := col_poly (PolyT.mul (PolyT.const 2) h) (PolyT.sub hg (PolyT.mul (PolyT.const 2) M)) (PolyT.const false) ha
  have E := eq_poly ha
  unfold linkedGate
  exact PolyT.ite' (PolyT.decide_lt hg (PolyT.mul (PolyT.const 2) M)) A
    (PolyT.ite' (PolyT.decide_lt hg S) C E)
private theorem localPoly {c : α → Code} {g : α → ℕ} {a : α → W} (C : PC c) (un : Unary (fun x => (c x).ne)) (hg : PolyT g) (ha : PolyT a) : PolyT fun x => localPorts (c x) (g x) (a x) := by
  have fst := PolyT.fst (PolyT.id' (α:=α × ℕ));have gt := C.gate fst (PolyT.snd PolyT.id');have v := PolyT.comp hg fst
  exact PolyT.zip (PolyT.map (C.bit fst (PolyT.snd PolyT.id')) (PolyT.filter (f:=fun x e => (c x).gate e == g x) (by fun_prop) (PolyT.range un))) ha
private theorem pin_poly {n : α → ℕ} {ps : α → List (ℕ × Bool)} {ix : α → ℕ → ℕ} {val : α → ℕ → Bool} (hu : Unary n) (hp : PolyT ps) (hi : PolyT fun x : α × ℕ => ix x.1 x.2) (hv : PolyT fun x : α × ℕ => val x.1 x.2) : PolyT fun x => pin (n x) (ps x) (ix x) (val x) := by
  unfold pin
  apply PolyT.all (f := fun x (t : ℕ × Bool) => (List.range (n x)).all fun i => decide (t.1=ix x i → t.2=val x i)) _ hp
  apply PolyT.all (f := fun (x : α × (ℕ × Bool)) i => decide (x.2.1 = ix x.1 i → x.2.2 = val x.1 i)) _ (PolyT.comp (PolyT.range hu) (PolyT.fst PolyT.id'))
  let f (x : (α × (ℕ × Bool)) × ℕ) := (x.1.1,x.2)
  have hf : PolyT f := by unfold f;fun_prop
  have I := PolyT.comp hi hf
  have V := PolyT.comp hv hf
  exact decide_imp (PolyT.decide_eq (PolyT.fst (PolyT.snd (PolyT.fst PolyT.id'))) I) (PolyT.decide_eq (PolyT.snd (PolyT.snd (PolyT.fst PolyT.id'))) V)
private theorem edgeRanges {D K : α → ℕ} (hd : Unary D) (hk : Unary K) : Unary (fun x => (slot (D x) (K x)).ne) ∧ Unary (fun x => (stage (D x)).ne) := by
  have B := umul (uconst 2000000) (uadd (uadd hd hk) (uconst 1))
  have hs := (pc_slot (dpoly hd) (dpoly hk)).ne
  have ht := (pc_stage (dpoly hd)).ne
  have bounds (x : α) := sizes 1 (D x) (K x) 0
  constructor
  all_goals apply Unary.of_le B (by assumption); intro x; have h := bounds x; dsimp only at h
            have hne := (Nat.le_add_left (whole 1 (D x) (K x) 0).ne _).trans h
            simp only [whole,M3B.ECLayout.code,arith,chains,base,splice,sum,repeatCode] at hne
            change _ ≤ 2000000*(D x+K x+1);omega
attribute [local fun_prop] PolyT.const PolyT.fst PolyT.snd PolyT.id' PolyT.getD PolyT.toNat' PolyT.decide_eq PolyT.ite' PolyT.ofBits PolyT.comp DetDLP_W1_Queries.first_poly DetDLP_W1_Queries.more_poly m89_enum_words.fields_poly
private theorem unLen : Unary len := by
  have um : Unary m := by unfold m; apply Unary.of_length; unfold field fld; fun_prop
  exact uadd (uadd (umul (uconst 4) (umul (uconst 2) um)) (uconst 2)) (uconst 1)
private theorem indPoly {α : Type} [Enc α] {n : α → ℕ} {b : α → Bool} (hn : Unary n) (hb : PolyT b) : PolyT (fun x => indicator (n x) (b x)) := by
  apply w5_M6Sort.encode_poly
  apply PolyT.map (f:=fun x (j : ℕ) => if j=0 then (b x).toNat else 0) _ (PolyT.range hn)
  exact PolyT.ite' (PolyT.decide_eq (PolyT.snd PolyT.id') (PolyT.const 0)) (PolyT.toNat' (PolyT.comp hb (PolyT.fst PolyT.id'))) (PolyT.const 0)
attribute [local fun_prop] w5_M6Sort.decode_poly PolyT.bits
private theorem spin {D p : α → ℕ} {ps : α → List (ℕ × Bool)} (hd : Unary D) (hp : PolyT p) (hs : PolyT ps) : PolyT fun x => stagePins (D x) (p x) (ps x) := by
  have f := PolyT.fst (PolyT.id' (α:=α × ℕ)); have i := PolyT.snd (PolyT.id' (α:=α × ℕ))
  have d := PolyT.comp (dpoly hd) f; have n := mul_poly.nb d
  have A := pin_poly (ix:=fun x j => (mul (D x)).nb+(D x+j)) (val:=fun x i => (p x).testBit i) hd hs (PolyT.add n (PolyT.add d i)) (PolyT.testBit (PolyT.comp hp f) i)
  have B := pin_poly (ix:=fun x j => addrN (D x) (D x+j) 1) (val:=fun _ _ => false) hd hs (PolyT.add (PolyT.add (PolyT.mul (PolyT.const 2) n) (PolyT.mul (PolyT.const 4) (PolyT.add d i))) (PolyT.const 1)) (PolyT.const false)
  exact PolyT.and' A B
private theorem sgate {D K p T s b g : α → ℕ} {a : α → W} (hd : Unary D) (hk : Unary K) (hp : PolyT p) (ht : PolyT T) (hs : PolyT s) (hb : PolyT b) (hg : PolyT g) (ha : PolyT a) : PolyT fun x => slotGate (D x) (K x) (p x) (T x) (s x) (b x) (g x) (a x) := by
  have d := dpoly hd; have k := dpoly hk; have L := pc_linked d; have n := L.ng; have nb := L.nb
  have E := PolyT.add n (PolyT.mul (PolyT.const 8) (PolyT.add d (PolyT.const 1)))
  have ph := PolyT.add (PolyT.add E (PolyT.mul (PolyT.const 3) d)) (PolyT.mul (PolyT.const 5) (PolyT.add d (PolyT.const 1)))
  have ps := localPoly (pc_slot d k) (edgeRanges hd hk).1 hg ha
  have inner := PolyT.ite' (PolyT.decide_lt hg n) (PolyT.and' (linkedChk hd hg ha) (spin hd hp ps)) (PolyT.ite' (PolyT.decide_lt hg E) (rows_poly d hp ht (PolyT.sub hg n) ha) (eq_poly ha))
  have f := PolyT.fst (PolyT.id' (α:=α × ℕ)); have i := PolyT.snd (PolyT.id' (α:=α × ℕ)); have N := PolyT.comp nb f; have D' := PolyT.comp d f
  have P := pin_poly (ix:=fun x j => (linked (D x)).nb+4*j) (val:=fun x j => (s x).testBit j) hd ps (by fun_prop) (PolyT.testBit (PolyT.comp hs f) i)
  have Q := pin_poly (ix:=fun x j => (linked (D x)).nb+4*(5*(D x+1)+j)+1) (val:=fun x j => (b x).testBit j) hd ps (by fun_prop) (PolyT.testBit (PolyT.comp hb f) i)
  have R := PolyT.ite' (PolyT.decide_lt hg ph) (PolyT.and' (PolyT.and' inner P) Q) (PolyT.ite' (PolyT.decide_lt hg (PolyT.add ph k)) (PolyT.or' (PolyT.decide_lt (PolyT.sub hg ph) (PolyT.add d (PolyT.const 1))) (PolyT.not' (PolyT.getD ha (PolyT.const 0) (PolyT.const false)))) (eq_poly ha))
  exact R
private theorem tgate {D p s g : α → ℕ} {first : α → Bool} {a : α → W} (hd : Unary D) (hp : PolyT p) (hs : PolyT s) (hg : PolyT g) (hf : PolyT first) (ha : PolyT a) : PolyT fun x => stageGate (D x) (p x) (s x) (g x) (first x) (a x) := by
  have d := dpoly hd; have n := (pc_linked d).ng; have i := PolyT.sub hg n
  have ps := localPoly (pc_stage d) (edgeRanges hd (uconst 0)).2 hg ha
  have E := PolyT.decide_and (PolyT.decide_eq (PolyT.getD ha (PolyT.const 2) (PolyT.const false)) (PolyT.testBit hp i)) (decide_imp (PolyT.decide_eq i d) (PolyT.decide_eq (PolyT.getD ha (PolyT.const 0) (PolyT.const false)) (PolyT.const false)))
  have inner := PolyT.ite' (PolyT.decide_lt hg n) (PolyT.and' (linkedChk hd hg ha) (spin hd hp ps)) (PolyT.ite' (PolyT.decide_lt hg (PolyT.add (PolyT.add n d) (PolyT.const 1))) (PolyT.and' (col_poly (PolyT.add d (PolyT.const 1)) i (PolyT.const true) ha) E) (eq_poly ha))
  have f := PolyT.fst (PolyT.id' (α:=α × ℕ)); have j := PolyT.snd (PolyT.id' (α:=α × ℕ))
  have P := pin_poly (ix:=fun _ j => j) (val:=fun x j => (s x).testBit j) hd ps j (PolyT.testBit (PolyT.comp hs f) j)
  exact PolyT.and' inner (PolyT.or' (PolyT.not' hf) P)
private theorem ord {w : α → W} {g : α → ℕ} {a : α → W} (hw : PolyT w) (hg : PolyT g) (ha : PolyT a) : PolyT fun x => ordinary (w x) (g x) (a x) := by
  have hd : Unary (fun x => d (w x)) := by unfold d width; apply Unary.of_length; unfold prime num nums field fld; fun_prop
  have hk : Unary (fun x => k (w x)) := by unfold k width; apply Unary.of_length; unfold threshold num nums field fld; fun_prop
  have dd := dpoly hd; have kk := dpoly hk; have mm := PolyT.comp params.2.1 hw; have pr := PolyT.comp params.2.2.2.1 hw
  have sn := (pc_slot dd kk).ng; have tn := (pc_stage dd).ng; have m4 := PolyT.mul (PolyT.const 4) mm; have m2 := PolyT.mul (PolyT.const 2) mm
  have N := PolyT.mul m4 sn; have End := PolyT.add N (PolyT.mul m4 tn); have L := (pc_chains mm dd kk).ng
  have cs : PolyT (fun x => nums (field (w x) 1)) := by unfold nums field fld;fun_prop
  have P : PolyT (fun x => prime (w x)) := by unfold prime num nums field fld; fun_prop
  have T : PolyT (fun x => threshold (w x)) := by unfold threshold num nums field fld; fun_prop
  have tar : PolyT (fun x => target (w x)) := by unfold target num nums field fld; fun_prop
  have i2 := PolyT.mul (PolyT.const 2) (PolyT.mod (PolyT.div hg sn) mm)
  have sg := sgate hd hk P T (PolyT.sub (PolyT.getD cs i2 (PolyT.const 0)) (PolyT.const 1)) (PolyT.getD cs (PolyT.add i2 (PolyT.const 1)) (PolyT.const 0)) (PolyT.mod hg sn) ha
  have J := PolyT.div (PolyT.sub hg N) tn
  have tg := tgate hd P (PolyT.ite' (PolyT.decide_lt J m2) tar (PolyT.const 1)) (PolyT.mod (PolyT.sub hg N) tn) (PolyT.decide_eq (PolyT.mod J m2) (PolyT.const 0)) ha
  have plen := PolyT.length pr; have cap := PolyT.mul m4 dd; have np := PolyT.ite' (PolyT.decide_le plen cap) plen cap
  have b := PolyT.getD ha (PolyT.const 0) (PolyT.const false)
  have R := PolyT.ite' (PolyT.decide_lt hg N) sg (PolyT.ite' (PolyT.decide_lt hg End) tg (PolyT.ite' (PolyT.decide_lt hg L) (eq_poly ha) (PolyT.ite' (PolyT.decide_lt hg (PolyT.add L np)) (PolyT.beq' b (PolyT.getD pr (PolyT.sub hg L) (PolyT.const false))) (PolyT.ite' (PolyT.decide_eq hg (PolyT.add L np)) (PolyT.decide_and (PolyT.decide_le plen cap) (PolyT.decide_eq b (PolyT.const false))) (eq_poly ha)))))
  apply R.congr; intro x; simp only [ordinary, Nat.min_def, bit]; split <;> rename_i h
  · rfl
  · split <;> rfl
theorem fpEntry_ordinary_poly : PolyT (fun z : List Bool × ℕ × List Bool => indicator (len z.1) (ordinary z.1 z.2.1 z.2.2)) := by
  have f := PolyT.fst (PolyT.id' (α:=W × ℕ × W)); have s := PolyT.snd (PolyT.id' (α:=W × ℕ × W))
  have ul := PolyT.comp (show PolyT (fun z => List.replicate (len z) ()) from unLen) f
  have b := ord f (PolyT.fst s) (PolyT.snd s)
  have R := indPoly (n:=fun z : W × ℕ × W => len z.1) ul b
  exact R
end DetDLP.M3A.FpPolyDefs
abbrev solution := DetDLP.M3A.FpPolyDefs.fpEntry_ordinary_poly
