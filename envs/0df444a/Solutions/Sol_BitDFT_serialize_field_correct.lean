-- Prove2me | solution 1 for BitDFT.serialize_field_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:21:35.899233+00:00
-- url     : https://prove2.me/submissions/d1dbc663-d495-4657-ac0a-7ff20fbeb026

import Definitions.Def_BitDFT_SerializeField
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.GetD

namespace BitDFT.SerializeField
open IntMul

private theorem cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem protect_same (a : Sym) (d : Move)
    (h : a = .start → d ≠ .left) : protect a (a,d) = (a,d) := by
  by_cases ha : a = .start
  · simp [protect, HeaderReader.protect, ha, h ha]
  · simp [protect, HeaderReader.protect, ha]

private theorem positive_not_start (w : List Bool) (p : ℕ) (hp : 0 < p) :
    machine.tapeOf (w.map machine.bitSym) p ≠ TapeCopy.Sym.start := by
  cases p with
  | zero => omega
  | succ p =>
    simp only [MultitapeTM.tapeOf]
    by_cases h : p < w.length
    · rw [List.getD_eq_getElem _ _ (by simpa using h)]
      simp only [List.getElem_map]
      cases w[p] <;> decide
    · rw [List.getD_eq_default _ _ (by simpa using (Nat.le_of_not_gt h))]
      decide

private theorem tape_append (w : List Sym) (a : Sym) :
    Function.update (machine.tapeOf w) (w.length + 1) a = machine.tapeOf (w ++ [a]) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    by_cases hp : p = w.length
    · subst p; simp [MultitapeTM.tapeOf, List.getD_append_right]
    · rw [Function.update_of_ne (by omega : p+1 ≠ w.length+1)]
      simp only [MultitapeTM.tapeOf]
      by_cases hlt : p < w.length
      · rw [List.getD_append _ _ _ _ hlt]
      · have hge : w.length ≤ p := by omega
        rw [List.getD_eq_default _ _ hge, List.getD_append_right _ _ _ _ hge]
        exact (List.getD_eq_default _ _ (by simp; omega)).symm

private theorem write_step (base : machine.Cfg) (q q' : State) (v out : List Bool)
    (p p' : ℕ) (b : Bool) (d : Move)
    (ht : transition q (fun i => (frame base q v out p).cells i ((frame base q v out p).head i)) =
      (q',fun i => (if i = 1 then machine.bitSym b else (frame base q v out p).cells i ((frame base q v out p).head i),
        if i = 1 then Move.right else if i = 4 then d else Move.stay)))
    (hp : (match d with | .left => p-1 | .stay => p | .right => p+1) = p') :
    machine.step (frame base q v out p) = frame base q' v (out++[b]) p' := by
  let c := frame base q v out p
  change transition c.state (fun i => c.cells i (c.head i)) = _ at ht
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · simpa [c,frame,List.map_append] using tape_append (out.map machine.bitSym) (machine.bitSym b)
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [c,frame]
    cases d <;> exact hp

private theorem keep_step (base : machine.Cfg) (q q' : State) (v out : List Bool)
    (p p' : ℕ) (d : Move)
    (ht : transition q (fun i => (frame base q v out p).cells i ((frame base q v out p).head i)) =
      (q',fun i => ((frame base q v out p).cells i ((frame base q v out p).head i),
        if i = 4 then d else Move.stay)))
    (hp : (match d with | .left => p-1 | .stay => p | .right => p+1) = p') :
    machine.step (frame base q v out p) = frame base q' v out p' := by
  let c := frame base q v out p
  change transition c.state (fun i => c.cells i (c.head i)) = _ at ht
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [c,frame]
    cases d <;> exact hp

theorem start_step (base : machine.Cfg) (v out : List Bool) :
    machine.step (frame base .start v out (v.length+1)) = frame base .unary v out v.length := by
  apply keep_step _ _ _ _ _ _ _ .left _ (by simp)
  apply Prod.ext
  · rfl
  · funext i
    change protect _ (_,_) = _
    apply protect_same
    by_cases hi : i = 4
    · subst i
      intro h
      exact False.elim (positive_not_start v (v.length+1) (by omega) h)
    · simp [hi]

theorem unary_step (base : machine.Cfg) (v out : List Bool) (p : ℕ) :
    machine.step (frame base .unary v out (p+1)) = frame base .unary v (out++[true]) p := by
  let c := frame base .unary v out (p+1)
  have h1 : c.cells 1 (c.head 1) = TapeCopy.Sym.blank := by simp [c,frame,MultitapeTM.tapeOf]
  have h4 : c.cells 4 (c.head 4) ≠ TapeCopy.Sym.start := positive_not_start v (p+1) (by omega)
  apply write_step _ _ _ _ _ _ _ true .left _ (by simp)
  apply Prod.ext
  · change (raw .unary (fun i => c.cells i (c.head i))).1 = _
    simp [raw,h4]
  · funext i
    change protect (c.cells i (c.head i)) ((raw .unary (fun j => c.cells j (c.head j))).2 i) = _
    simp only [raw,h4,if_false]
    fin_cases i
    · exact protect_same _ _ (by intro _; decide)
    · simp [h1,protect,HeaderReader.protect,MultitapeTM.bitSym]
    · exact protect_same _ _ (by intro _; decide)
    · exact protect_same _ _ (by intro _; decide)
    · apply protect_same; exact fun h => False.elim (h4 h)

theorem delimiter_step (base : machine.Cfg) (v out : List Bool) :
    machine.step (frame base .unary v out 0) = frame base .copy v (out++[false]) 1 := by
  let c := frame base .unary v out 0
  have h1 : c.cells 1 (c.head 1) = TapeCopy.Sym.blank := by simp [c,frame,MultitapeTM.tapeOf]
  have h4 : c.cells 4 (c.head 4) = TapeCopy.Sym.start := rfl
  apply write_step _ _ _ _ _ _ _ false .right _ rfl
  apply Prod.ext
  · change (raw .unary (fun i => c.cells i (c.head i))).1 = _
    simp [raw,h4]
  · funext i
    change protect (c.cells i (c.head i)) ((raw .unary (fun j => c.cells j (c.head j))).2 i) = _
    simp only [raw,h4,if_true]
    fin_cases i
    · exact protect_same _ _ (by intro _; decide)
    · simp [h1,protect,HeaderReader.protect,MultitapeTM.bitSym]
    · exact protect_same _ _ (by intro _; decide)
    · exact protect_same _ _ (by intro _; decide)
    · exact protect_same _ _ (by intro _; decide)

theorem copy_step (base : machine.Cfg) (pre : List Bool) (b : Bool) (rest out : List Bool) :
    machine.step (frame base .copy (pre++b::rest) out (pre.length+1)) =
      frame base .copy (pre++b::rest) (out++[b]) (pre.length+2) := by
  let c := frame base .copy (pre++b::rest) out (pre.length+1)
  have h1 : c.cells 1 (c.head 1) = TapeCopy.Sym.blank := by simp [c,frame,MultitapeTM.tapeOf]
  have h4 : c.cells 4 (c.head 4) = machine.bitSym b := by simp [c,frame,MultitapeTM.tapeOf]
  have hb : c.cells 4 (c.head 4) = TapeCopy.Sym.zero ∨ c.cells 4 (c.head 4) = TapeCopy.Sym.one := by
    rw [h4]; cases b <;> simp [MultitapeTM.bitSym]
  apply write_step _ _ _ _ _ _ _ b .right _ (by simp)
  apply Prod.ext
  · change (raw .copy (fun i => c.cells i (c.head i))).1 = _
    simp [raw,hb]
  · funext i
    change protect (c.cells i (c.head i)) ((raw .copy (fun j => c.cells j (c.head j))).2 i) = _
    simp only [raw,hb,if_true]
    fin_cases i
    · exact protect_same _ _ (by intro _; decide)
    · simp [h1,h4,protect,HeaderReader.protect]; cases b <;> simp [MultitapeTM.bitSym]
    · exact protect_same _ _ (by intro _; decide)
    · exact protect_same _ _ (by intro _; decide)
    · exact protect_same _ _ (by intro _; decide)

theorem copy_done (base : machine.Cfg) (v out : List Bool) :
    machine.step (frame base .copy v out (v.length+1)) = frame base .halt v out (v.length+1) := by
  let c := frame base .copy v out (v.length+1)
  have h4 : c.cells 4 (c.head 4) = TapeCopy.Sym.blank := by simp [c,frame,MultitapeTM.tapeOf]
  apply keep_step _ _ _ _ _ _ _ .stay _ rfl
  apply Prod.ext
  · change (raw .copy (fun i => c.cells i (c.head i))).1 = _
    simp [raw,h4]
  · funext i
    change protect (c.cells i (c.head i)) ((raw .copy (fun j => c.cells j (c.head j))).2 i) = _
    simp only [raw,h4,reduceCtorEq,or_self,if_false,ite_self]
    exact protect_same _ .stay (by intro _; decide)

theorem unary_run (base : machine.Cfg) (v out : List Bool) (p : ℕ) :
    machine.step^[p] (frame base .unary v out p) =
      frame base .unary v (out++List.replicate p true) 0 := by
  induction p generalizing out with
  | zero => simp
  | succ p ih =>
    rw [Function.iterate_succ_apply,unary_step,ih]
    simp [List.replicate_succ,List.append_assoc]

theorem copy_run (base : machine.Cfg) (pre rest out : List Bool) :
    machine.step^[rest.length] (frame base .copy (pre++rest) out (pre.length+1)) =
      frame base .copy (pre++rest) (out++rest) (pre.length+rest.length+1) := by
  induction rest generalizing pre out with
  | nil => simp
  | cons b rest ih =>
    rw [List.length_cons,Function.iterate_succ_apply,copy_step]
    have h := ih (pre++[b]) (out++[b])
    simpa [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem serialize_run (base : machine.Cfg) (v out : List Bool) :
    machine.step^[2*v.length+3] (frame base .start v out (v.length+1)) =
      frame base .halt v (out++List.replicate v.length true++false::v) (v.length+1) := by
  let c := frame base .start v out (v.length+1)
  have ht : machine.step^[2*v.length+3] c =
      machine.step^[1] (machine.step^[v.length] (machine.step^[1]
        (machine.step^[v.length] (machine.step^[1] c)))) := by
    simp only [← Function.iterate_add_apply]
    congr 1
    omega
  rw [ht]
  simp only [Function.iterate_one]
  rw [start_step,unary_run,delimiter_step]
  have hc := copy_run base [] v (out++List.replicate v.length true++[false])
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hc
  rw [hc,copy_done]
  simp [List.append_assoc]

end BitDFT.SerializeField



open BitDFT.SerializeField IntMul

theorem solution (base : machine.Cfg) (v out : List Bool) :
    machine.step^[2*v.length+3] (frame base .start v out (v.length+1)) =
      frame base .halt v (out++List.replicate v.length true++false::v) (v.length+1) := by
  exact serialize_run base v out
