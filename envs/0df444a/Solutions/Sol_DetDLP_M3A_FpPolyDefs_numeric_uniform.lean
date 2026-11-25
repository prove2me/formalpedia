-- Prove2me | solution 1 for DetDLP.M3A.FpPolyDefs.numeric_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T21:33:26.785679+00:00
-- url     : https://prove2.me/submissions/8bf25e91-571d-41b2-aa9a-06d0d4e1a251

import Definitions.Def_DetDLP_M3A_FpPolyDefs
set_option autoImplicit false
namespace DetDLP.M3A.FpPolyDefs
set_option maxHeartbeats 800000
attribute [local fun_prop] w4_M5Evaluator.n0_poly w4_M5Evaluator.J_poly w4_M5Evaluator.L1_poly w4_M5Evaluator.L2_poly
open Groundwork S8H.PointAddresses S8L.FpPair.Address
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

theorem numeric_uniform {m d k n e : α → ℕ} (hm : PolyT m) (hd : PolyT d) (hk : PolyT k) (hn : PolyT n) (he : PolyT e) :
    let c := fun x => whole (m x) (d x) (k x) (n x)
    PolyT (fun x => (c x).ng) ∧ PolyT (fun x => (c x).nb) ∧ PolyT (fun x => (c x).ne) ∧ PolyT (fun x => (c x).gate (e x)) ∧ PolyT (fun x => (c x).bit (e x)) := by
  let C := pc_whole hm hd hk hn;exact ⟨C.ng,C.nb,C.ne,C.gate PolyT.id' he,C.bit PolyT.id' he⟩

end DetDLP.M3A.FpPolyDefs

abbrev solution := @DetDLP.M3A.FpPolyDefs.numeric_uniform
