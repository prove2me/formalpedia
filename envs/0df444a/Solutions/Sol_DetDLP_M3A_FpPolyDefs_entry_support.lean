-- Prove2me | solution 1 for DetDLP.M3A.FpPolyDefs.entry_support
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T00:06:42.481528+00:00
-- url     : https://prove2.me/submissions/021dd22e-846a-42a8-af09-942c3e3bb68c

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
structure PC {α : Type} [Enc α] (a : α → Code) : Prop where
  ng : PolyT fun x => (a x).ng
  nb : PolyT fun x => (a x).nb
  ne : PolyT fun x => (a x).ne
  gate : ∀ {β : Type} [Enc β] {h : β → α} {e : β → ℕ}, PolyT h → PolyT e → PolyT fun x => (a (h x)).gate (e x)
  bit : ∀ {β : Type} [Enc β] {h : β → α} {e : β → ℕ}, PolyT h → PolyT e → PolyT fun x => (a (h x)).bit (e x)
variable {α : Type} [Enc α]
theorem ofUnif {c : ℕ → Code} {d : α → ℕ} (h : Uniform c) (hd : PolyT d) : PC (fun x => c (d x)) :=
  ⟨h.ng hd,h.nb hd,h.ne hd,fun hh he => h.gate (PolyT.comp hd hh) he,fun hh he => h.bit (PolyT.comp hd hh) he⟩
theorem pc_sum {a b : α → Code} (h : PC a) (k : PC b) : PC (fun x => sum (a x) (b x)) := by
  constructor
  · exact PolyT.add h.ng k.ng
  · exact PolyT.add h.nb k.nb
  · exact PolyT.add h.ne k.ne
  · intro β _ f e hf he; have hn := PolyT.comp h.ne hf;have hg := PolyT.comp h.ng hf
    exact PolyT.ite' (PolyT.decide_lt he hn) (h.gate hf he) (PolyT.add hg (k.gate hf (PolyT.sub he hn)))
  · intro β _ f e hf he; have hn := PolyT.comp h.ne hf;have hb := PolyT.comp h.nb hf
    exact PolyT.ite' (PolyT.decide_lt he hn) (h.bit hf he) (PolyT.add hb (k.bit hf (PolyT.sub he hn)))
theorem pc_splice {a : α → Code} {n : α → ℕ} {l r : α → ℕ → ℕ} (h : PC a) (hn : PolyT n) (hl : PolyT fun z : α × ℕ => l z.1 z.2) (hr : PolyT fun z : α × ℕ => r z.1 z.2) : PC (fun x => splice (a x) (n x) (l x) (r x)) := by
  constructor
  · exact PolyT.add h.ng hn
  · exact h.nb
  · exact PolyT.add h.ne (PolyT.add hn hn)
  all_goals intro β _ f e hf he; have ha := PolyT.comp h.ne hf; have hn' := PolyT.comp hn hf; have hg := PolyT.comp h.ng hf; have hu := PolyT.sub he ha; simp only [splice]
  · exact PolyT.ite' (PolyT.decide_lt he ha) (h.gate hf he) (PolyT.add hg (PolyT.ite' (PolyT.decide_lt hu hn') hu (PolyT.sub hu hn')))
  · exact PolyT.ite' (PolyT.decide_lt he ha) (h.bit hf he) (PolyT.ite' (PolyT.decide_lt hu hn') (PolyT.comp hl (PolyT.prodMk hf hu)) (PolyT.comp hr (PolyT.prodMk hf (PolyT.sub hu hn'))))
theorem pc_repeat {a : α → Code} {n : α → ℕ} (h : PC a) (hn : PolyT n) : PC (fun x => repeatCode (n x) (a x)) := by
  refine ⟨PolyT.mul hn h.ng,PolyT.mul hn h.nb,PolyT.mul hn h.ne,?_,?_⟩
  all_goals intro β _ f e hf he;have hn' := PolyT.comp h.ne hf;have hg := PolyT.comp h.ng hf;have hb := PolyT.comp h.nb hf
  · exact PolyT.add (h.gate hf (PolyT.mod he hn')) (PolyT.mul hg (PolyT.div he hn'))
  · exact PolyT.add (h.bit hf (PolyT.mod he hn')) (PolyT.mul hb (PolyT.div he hn'))
theorem pc_anchor {k : α → ℕ} (hk : PolyT k) : PC fun x => S8H0.AnchoredLayout.anchorCode (k x) := ⟨hk,hk,hk,fun _ he => he,fun _ he => he⟩
theorem pc_linked {d : α → ℕ} (hd : PolyT d) : PC (fun x => linked (d x)) := by
  apply pc_splice (ofUnif stage_poly hd) (PolyT.mul (PolyT.const 4) hd)
  all_goals have hh := PolyT.comp hd (PolyT.fst (PolyT.id' (α:=α × ℕ)));have H := mul_poly.nb hh;simp only [addrN,w4_M5EdgeNat.edgeBase,w4_M5GraphBounds.W];fun_prop
theorem pc_stage {d : α → ℕ} (hd : PolyT d) : PC (fun x => stage (d x)) := by
  apply pc_splice (pc_sum (pc_linked hd) (ofUnif (add_poly (·+1) (by intros;fun_prop)) hd)) hd
  all_goals have hh := PolyT.comp hd (PolyT.fst (PolyT.id' (α:=α × ℕ)));have H := (pc_linked hh).nb;have H' := mul_poly.nb hh;(try simp only [addrN]);fun_prop
def rawLink (d : ℕ) := splice (stageCode d) (2*d+2*d)
  (fun e => if e<2*d then (mul d).nb+(mul d).nb+(4*e+0) else (mul d).nb+(mul d).nb+(4*(e-2*d)+2))
  (fun e => if e<2*d then (mul d).nb+w4_M5EdgeNat.edgeBase d 9 e else w4_M5EdgeNat.edgeBase d 9 (e-2*d))
def rawRow (d j l i : ℕ) := (stageCode d).nb+(4*(i+(d+1)*j)+l)
def rawPhys (d : ℕ) := splice (sum (rawLink d) (add (8*(d+1)))) (3*d+5*(d+1))
  (fun e => if e<3*d then rawRow d (if e/d=0 then 0 else if e/d=1 then 1 else 5) (if e/d<2 then 2 else 0) (e%d)
    else let t := e-3*d;let j := t/(d+1);let i := t%(d+1);rawRow d (if j=0 then 1 else if j=1 then 3 else if j=2 then 4 else if j=3 then 5 else 7) (if j=0 then 2 else if j=3 then 2 else if j=4 then 1 else 0) i)
  (fun e => if e<3*d then (if e/d=0 then e%d else if e/d=1 then d+e%d else (mul d).nb+(mul d).nb+(4*(e%d)+1))
    else let t := e-3*d;let j := t/(d+1);let i := t%(d+1);rawRow d (if j=0 then 2 else if j=2 then 5 else 6) (if j=3 then 2 else if j=4 then 1 else 0) i)
theorem pc_raw {d : α → ℕ} (hd : PolyT d) : PC (fun x => rawPhys (d x)) := by
  have L : PC (fun x => rawLink (d x)) := by
    apply pc_splice (ofUnif stage_poly hd) (by fun_prop)
    all_goals have hh := PolyT.comp hd (PolyT.fst (PolyT.id' (α:=α × ℕ)));have H := mul_poly.nb hh;(try simp only [w4_M5EdgeNat.edgeBase,w4_M5GraphBounds.W]); fun_prop
  apply pc_splice (pc_sum L (ofUnif (add_poly (fun x => 8*(x+1)) (by intros;fun_prop)) hd)) (by fun_prop)
  all_goals have hh := PolyT.comp hd (PolyT.fst (PolyT.id' (α:=α × ℕ))); have H := mul_poly.nb hh;have H' := stage_poly.nb hh; simp only [rawRow];fun_prop
theorem pc_slot {d k : α → ℕ} (hd : PolyT d) (hk : PolyT k) : PC (fun x => slot (d x) (k x)) := by
  apply pc_splice (pc_sum (pc_raw hd) (pc_anchor hk)) (hn:=show PolyT (fun x => min (k x) (d x+1)) by simp only [Nat.min_def];fun_prop)
  · have H := stage_poly.nb (PolyT.comp hd (PolyT.fst (PolyT.id' (α:=α × ℕ))));change PolyT fun z : α × ℕ => rawRow (d z.1) 3 0 z.2;unfold rawRow;fun_prop
  · have H := (pc_raw (PolyT.comp hd (PolyT.fst (PolyT.id' (α:=α × ℕ))))).nb;exact PolyT.add H (PolyT.snd PolyT.id')

theorem pc_base {m d k : α → ℕ} (hm : PolyT m) (hd : PolyT d) (hk : PolyT k) : PC (fun x => base (m x) (d x) (k x)) := by
  let h := pc_repeat (pc_stage hd) (PolyT.mul (PolyT.const 2) hm)
  exact pc_sum (pc_repeat (pc_slot hd hk) (PolyT.mul (PolyT.const 4) hm)) (pc_sum h h)
theorem pc_chains {m d k : α → ℕ} (hm : PolyT m) (hd : PolyT d) (hk : PolyT k) : PC (fun x => chains (m x) (d x) (k x)) := by
  apply pc_splice (pc_base hm hd hk) (by fun_prop)
  all_goals have hd' := PolyT.comp hd (PolyT.fst (PolyT.id' (α:=α × ℕ)));have hm' := PolyT.comp hm (PolyT.fst (PolyT.id' (α:=α × ℕ)));have hk' := PolyT.comp hk (PolyT.fst (PolyT.id' (α:=α × ℕ)));have H := (pc_slot hd' hk').nb; have U := (pc_linked hd').nb;have V := (pc_stage hd').nb
            simp only [tie,sPort,xPort,Bool.false_eq_true,if_true,if_false];fun_prop
theorem pc_arith {m d k n : α → ℕ} (hm : PolyT m) (hd : PolyT d) (hk : PolyT k) (hn : PolyT n) : PC (fun x => arith (m x) (d x) (k x) (n x)) := by
  have hmin : PolyT (fun x => min (n x) (4*m x*d x)) := by simp only [Nat.min_def];fun_prop
  apply pc_splice (pc_sum (pc_chains hm hd hk) (pc_anchor (PolyT.add hmin (PolyT.const 1)))) hmin
  · have hd' := PolyT.comp hd (PolyT.fst (PolyT.id' (α:=α × ℕ)));have hm' := PolyT.comp hm (PolyT.fst (PolyT.id' (α:=α × ℕ)));have hk' := PolyT.comp hk (PolyT.fst (PolyT.id' (α:=α × ℕ)));have H := (pc_slot hd' hk').nb; have U := (pc_linked hd').nb; simp only [prefixAddr,xPort];fun_prop
  · have H := PolyT.comp (pc_chains hm hd hk).nb (PolyT.fst (PolyT.id' (α:=α × ℕ)));exact PolyT.add H (PolyT.snd PolyT.id')
theorem pc_whole {m d k n : α → ℕ} (hm : PolyT m) (hd : PolyT d) (hk : PolyT k) (hn : PolyT n) : PC (fun x => whole (m x) (d x) (k x) (n x)) := by
  let C := pc_arith hm hd hk hn
  refine ⟨PolyT.add C.ng (PolyT.mul (PolyT.const 4) hm), C.nb, PolyT.add C.ne (PolyT.mul (PolyT.mul (PolyT.const 4) hm) hk),?_,?_⟩
  all_goals intro β _ f e hf he; have hd' := PolyT.comp hd hf;have hk' := PolyT.comp hk hf;have H := (pc_slot hd' hk').nb;have U := (pc_linked hd').nb;have hg := PolyT.comp C.ng hf;have hne := PolyT.comp C.ne hf;have hgate := C.gate hf he;have hbit := C.bit hf he
            simp only [whole,M3B.ECLayout.code,zPort];fun_prop

attribute [local fun_prop] PolyT.const PolyT.add PolyT.mul PolyT.sub PolyT.length PolyT.getD PolyT.id' PolyT.comp PolyT.bits PolyT.fst PolyT.snd PolyT.prodMk PolyT.map PolyT.append m89_enum_words.fields_poly w5_M6Sort.decode_poly w5_M6Sort.cw_poly DetDLP_W1_Queries.frame_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f
theorem uadd {α} [Enc α] {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary (fun x => f x+g x) := by
  apply (PolyT.append hf hg).congr;intro x;rw [List.replicate_add]
theorem umul {α} [Enc α] {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary (fun x => f x*g x) := by
  have H := PolyT.flatMap (f:=fun x (_ : Unit) => List.replicate (g x) ()) (PolyT.comp hg (PolyT.fst PolyT.id')) hf
  apply H.congr;intro x;change _ = List.replicate (f x*g x) ();generalize f x=n;induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ,List.flatMap_cons,ih,Nat.succ_mul];rw [← List.replicate_add,Nat.add_comm]
theorem uconst {α} [Enc α] (k : ℕ) : Unary (fun _ : α => k) := PolyT.const _
theorem sizes (M D K n : ℕ) : let c := whole M D K n; c.ng+c.nb+c.ne+c.ne ≤ 1000000*(M+1)*(D+K+n+1) := by
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
theorem params : PolyT d ∧ PolyT m ∧ PolyT k ∧ PolyT pre ∧ PolyT sizeField ∧ PolyT prec ∧ PolyT len := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | unfold d | unfold m | unfold k | unfold pre | unfold sizeField | unfold prec | unfold len
  all_goals dsimp only [d,m,k,pre,prec,len,width,num,field,nums,fld,prime,threshold,groupSize,dFilt];fun_prop
attribute [local fun_prop] PolyT.idxOf PolyT.filter PolyT.sum PolyT.all PolyT.getD PolyT.take PolyT.zip PolyT.testBit PolyT.ofBits PolyT.decide_and PolyT.decide_le PolyT.decide_lt PolyT.and' w4_M5GateOps.portList_poly w4_M5EdgeNat.srcNat_poly P2M_Groundwork_PolyT_cond__4c673073da15 PolyT.pow_unary
theorem products {xs : α → List ℕ} (h : PolyT xs) : PolyT (fun x => (xs x).foldl (·*·) 1) := by
  obtain ⟨s,hs,_,bound⟩ := PolyT.len_bound h
  refine PolyT.foldl_add h (PolyT.const 1) (by fun_prop) ⟨s,hs,fun x c e he => ?_⟩
  exact (PolyT.len_mul_le c e).trans (Nat.add_le_add_left ((Groundwork.len_le_of_mem he).trans (bound x)) _)
theorem coeff_poly {b : α → Bool} {z q j : α → ℕ} (hb : PolyT b) (hz : PolyT z) (hq : PolyT q) (hj : Unary j) : PolyT (fun x => coeff (b x) (z x) (q x) (j x)) := by
  have fst := PolyT.fst (PolyT.id' (α:=α × ℕ));have hb' := PolyT.comp hb fst;have hz' := PolyT.comp hz fst
  have r := PolyT.range hj
  have a := products (PolyT.map (f:=fun x i => if b x then z x-i else z x+i) (by fun_prop) r)
  have c := products (PolyT.map (f:=fun (_ : α) (i : ℕ) => i+1) (by fun_prop) r)
  simp only [List.foldl_map] at a c
  have ha : PolyT (fun x => magnitude (b x) (z x) (j x)) := PolyT.div a c
  have hj' : PolyT j := (PolyT.length r).congr (by intro x; simp)
  unfold coeff;fun_prop
theorem entry_support {α : Type} [Enc α] : PolyT d ∧ PolyT m ∧ PolyT k ∧ PolyT pre ∧ PolyT sizeField ∧ PolyT prec ∧ PolyT len := params
end DetDLP.M3A.FpPolyDefs

abbrev solution := @DetDLP.M3A.FpPolyDefs.entry_support
