-- Prove2me | solution 1 for BitDFT.two_tape_suffix_copy_blank_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T08:54:41.702824+00:00
-- url     : https://prove2.me/submissions/3489b557-fa91-43dd-b327-96a1dbf7a39c

import Definitions.Def_BitDFT_BlankEndCopyFrame
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul BitDFT BitDFT.SuffixCopyTwoTape

private theorem cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem tape_append (w : List Sym) (a : Sym) :
    Function.update (machine.tapeOf w) (w.length+1) a = machine.tapeOf (w++[a]) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
      by_cases hp : p = w.length
      · subst p
        simp [MultitapeTM.tapeOf,List.getD_append_right]
      · rw [Function.update_of_ne (by omega : p+1 ≠ w.length+1)]
        simp only [MultitapeTM.tapeOf]
        by_cases hlt : p < w.length
        · rw [List.getD_append _ _ _ _ hlt]
        · have hge : w.length ≤ p := by omega
          rw [List.getD_eq_default _ _ hge,List.getD_append_right _ _ _ _ hge]
          exact (List.getD_eq_default _ _ (by simp; omega)).symm

private theorem protect_stay (a : Sym) : protect a (a,Move.stay) = (a,Move.stay) := by
  by_cases h : a = .start <;> simp [protect,HeaderReader.protect,h]

private theorem copy_step_blank (base : machine.Cfg) (pre : List Bool)
    (b : Bool) (rest out : List Bool) :
    machine.step (blankEndFrame base .copy (pre ++ b::rest) out (pre.length+1)) =
      blankEndFrame base .copy (pre ++ b::rest) (out++[b]) (pre.length+2) := by
  let c := blankEndFrame base .copy (pre ++ b::rest) out (pre.length+1)
  have h0 : c.cells 0 (c.head 0) = machine.bitSym b := by
    simp [c,blankEndFrame,MultitapeTM.tapeOf,List.append_assoc]
  have h1 : c.cells 1 (c.head 1) = TapeCopy.Sym.blank := by
    simp [c,blankEndFrame,MultitapeTM.tapeOf]
  have hb : c.cells 0 (c.head 0) = TapeCopy.Sym.zero ∨
      c.cells 0 (c.head 0) = TapeCopy.Sym.one := by
    rw [h0]; cases b <;> simp [MultitapeTM.bitSym]
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.copy,fun i => (if i=1 then machine.bitSym b else c.cells i (c.head i),
        if i=0 ∨ i=1 then Move.right else Move.stay)) := by
    apply Prod.ext
    · change (raw .copy (fun i => c.cells i (c.head i))).1 = _
      simp [raw,hb]
    · funext i
      change protect (c.cells i (c.head i)) ((raw .copy (fun j => c.cells j (c.head j))).2 i) = _
      simp only [raw,hb,if_true]
      fin_cases i
      · simp [h0,protect,HeaderReader.protect]; cases b <;> simp [MultitapeTM.bitSym]
      · simp [h0,h1,protect,HeaderReader.protect]; cases b <;> simp [MultitapeTM.bitSym]
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · funext i
    fin_cases i
    · simp only [MultitapeTM.step,ht]
      exact Function.update_eq_self _ _
    · simp only [MultitapeTM.step,ht]
      change Function.update (c.cells 1) (c.head 1) (machine.bitSym b) = _
      rw [show c.cells 1 = machine.tapeOf (out.map machine.bitSym) by rfl]
      simpa [c,blankEndFrame,List.map_append] using
        tape_append (out.map machine.bitSym) (machine.bitSym b)
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [c,blankEndFrame]

private theorem copy_done_blank (base : machine.Cfg) (input out : List Bool) :
    machine.step (blankEndFrame base .copy input out (input.length+1)) =
      blankEndFrame base .halt input out (input.length+1) := by
  let c := blankEndFrame base .copy input out (input.length+1)
  have h0 : c.cells 0 (c.head 0) = TapeCopy.Sym.blank := by
    simp [c,blankEndFrame,MultitapeTM.tapeOf]
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.halt,fun i => (c.cells i (c.head i),Move.stay)) := by
    apply Prod.ext
    · change (raw .copy (fun i => c.cells i (c.head i))).1 = _
      simp [raw,h0]
    · funext i
      change protect (c.cells i (c.head i)) ((raw .copy (fun j => c.cells j (c.head j))).2 i) = _
      simp only [raw,h0,if_false]
      exact protect_stay _
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · funext i
    simp only [MultitapeTM.step,ht]
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]; rfl

theorem solution (base : machine.Cfg) (pre rest out : List Bool) :
    machine.step^[rest.length+1]
      (blankEndFrame base .copy (pre++rest) out (pre.length+1)) =
    blankEndFrame base .halt (pre++rest) (out++rest)
      (pre.length+rest.length+1) := by
  induction rest generalizing pre out with
  | nil =>
      simpa using copy_done_blank base pre out
  | cons b rest ih =>
      rw [List.length_cons,Function.iterate_succ_apply,copy_step_blank]
      have h := ih (pre++[b]) (out++[b])
      simpa [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

