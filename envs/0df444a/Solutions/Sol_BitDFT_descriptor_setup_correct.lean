-- Prove2me | solution 1 for BitDFT.descriptor_setup_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:04:28.629104+00:00
-- url     : https://prove2.me/submissions/2f068b29-092f-4e42-bab7-d38ac6bf169c

import Definitions.Def_BitDFT_DescriptorSetup
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases

namespace BitDFT.DescriptorSetup
open IntMul

private theorem cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem protect_same (a : Sym) (d : Move)
    (h : a = .start → d ≠ .left) : protect a (a,d) = (a,d) := by
  by_cases ha : a = .start
  · simp [protect, HeaderReader.protect, ha, h ha]
  · simp [protect, HeaderReader.protect, ha]

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

theorem copy_step (base : machine.Cfg) (pre : List Bool) (b : Bool) (rest : List Bool) :
    machine.step (frame base (pre++b::rest) pre.length) =
      frame base (pre++b::rest) (pre.length+1) := by
  let c := frame base (pre++b::rest) pre.length
  have hs : c.cells 1 (c.head 1) = machine.bitSym b := by
    simp [c,frame,MultitapeTM.tapeOf,List.append_assoc]
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.blank := by
    simp [c,frame,MultitapeTM.tapeOf]
  have h3 : c.cells 3 (c.head 3) = TapeCopy.Sym.blank := by
    simp [c,frame,MultitapeTM.tapeOf]
  have hb : c.cells 1 (c.head 1) = TapeCopy.Sym.zero ∨ c.cells 1 (c.head 1) = TapeCopy.Sym.one := by
    rw [hs]; cases b <;> simp [MultitapeTM.bitSym]
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.copy,fun i => (if i = 2 ∨ i = 3 then machine.bitSym b else c.cells i (c.head i),
        if i = 0 then Move.stay else Move.right)) := by
    apply Prod.ext
    · change (raw .copy (fun i => c.cells i (c.head i))).1 = _
      simp [raw,hb]
    · funext i
      change protect (c.cells i (c.head i)) ((raw .copy (fun j => c.cells j (c.head j))).2 i) = _
      simp only [raw,hb,if_true]
      fin_cases i
      · exact protect_same _ .stay (by intro _; decide)
      · exact protect_same _ .right (by intro _; decide)
      · simp [hs,h2,protect,HeaderReader.protect]; cases b <;> simp [MultitapeTM.bitSym]
      · simp [hs,h3,protect,HeaderReader.protect]; cases b <;> simp [MultitapeTM.bitSym]
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · simpa [c,frame,List.map_append,List.take_append,List.take_of_length_le (by simp : (pre.map machine.bitSym).length ≤ pre.length+1),Nat.add_assoc] using
        tape_append (TapeCopy.Sym.sep :: pre.map machine.bitSym) (machine.bitSym b)
    · simpa [c,frame,List.map_append,List.take_append,List.take_of_length_le (by simp : (pre.map machine.bitSym).length ≤ pre.length+1),Nat.add_assoc] using
        tape_append (TapeCopy.Sym.sep :: pre.map machine.bitSym) (machine.bitSym b)
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [c,frame]

theorem copy_run (base : machine.Cfg) (pre rest : List Bool) :
    machine.step^[rest.length] (frame base (pre++rest) pre.length) =
      frame base (pre++rest) (pre.length+rest.length) := by
  induction rest generalizing pre with
  | nil => simp
  | cons b rest ih =>
    rw [List.length_cons,Function.iterate_succ_apply,copy_step]
    have h := ih (pre++[b])
    simpa [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem copy_done (base : machine.Cfg) (y : List Bool) :
    machine.step (frame base y y.length) = final base y := by
  let c := frame base y y.length
  have hs : c.cells 1 (c.head 1) = TapeCopy.Sym.blank := by simp [c,frame,MultitapeTM.tapeOf]
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.blank := by simp [c,frame,MultitapeTM.tapeOf]
  have h3 : c.cells 3 (c.head 3) = TapeCopy.Sym.blank := by simp [c,frame,MultitapeTM.tapeOf]
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.halt,fun i => (if i = 2 ∨ i = 3 then TapeCopy.Sym.sep else c.cells i (c.head i),
        if i = 2 ∨ i = 3 then Move.left else Move.stay)) := by
    apply Prod.ext
    · change (raw .copy (fun i => c.cells i (c.head i))).1 = _
      simp [raw,hs]
    · funext i
      change protect (c.cells i (c.head i)) ((raw .copy (fun j => c.cells j (c.head j))).2 i) = _
      simp only [raw,hs,reduceCtorEq,or_self,if_false]
      fin_cases i
      · exact protect_same _ .stay (by intro _; decide)
      · exact protect_same _ .stay (by intro _; decide)
      · simp [h2,protect,HeaderReader.protect]
      · simp [h3,protect,HeaderReader.protect]
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · simpa [c,frame,final] using tape_append (TapeCopy.Sym.sep :: y.map machine.bitSym) TapeCopy.Sym.sep
    · simpa [c,frame,final] using tape_append (TapeCopy.Sym.sep :: y.map machine.bitSym) TapeCopy.Sym.sep
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [c,frame,final]


private def marked (base : machine.Cfg) (y : List Bool) : machine.Cfg where
  state := .mark
  cells := (initial base y).cells
  head := fun i => if i = 0 then base.head i else 1

private theorem start_step (base : machine.Cfg) (y : List Bool) :
    machine.step (initial base y) = marked base y := by
  let c := initial base y
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.mark,fun i => (c.cells i (c.head i),if i = 2 ∨ i = 3 then Move.right else Move.stay)) := by
    apply Prod.ext
    · rfl
    · funext i
      change protect (c.cells i (c.head i)) (c.cells i (c.head i),_) = _
      apply protect_same
      intro _
      split <;> decide
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [c,initial,marked]

private theorem mark_step (base : machine.Cfg) (y : List Bool) :
    machine.step (marked base y) = frame base y 0 := by
  let c := marked base y
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.blank := by simp [c,marked,initial,MultitapeTM.tapeOf]
  have h3 : c.cells 3 (c.head 3) = TapeCopy.Sym.blank := by simp [c,marked,initial,MultitapeTM.tapeOf]
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.copy,fun i => (if i = 2 ∨ i = 3 then TapeCopy.Sym.sep else c.cells i (c.head i),
        if i = 2 ∨ i = 3 then Move.right else Move.stay)) := by
    apply Prod.ext
    · rfl
    · funext i
      change protect (c.cells i (c.head i)) ((raw .mark (fun j => c.cells j (c.head j))).2 i) = _
      simp only [raw]
      fin_cases i
      · exact protect_same _ .stay (by intro _; decide)
      · exact protect_same _ .stay (by intro _; decide)
      · simp [h2,protect,HeaderReader.protect]
      · simp [h3,protect,HeaderReader.protect]
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · simpa [c,marked,initial,frame] using tape_append [] TapeCopy.Sym.sep
    · simpa [c,marked,initial,frame] using tape_append [] TapeCopy.Sym.sep
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [c,marked,initial,frame]

end BitDFT.DescriptorSetup
open BitDFT.DescriptorSetup IntMul

theorem solution (base : machine.Cfg) (y : List Bool) :
    machine.step^[y.length+3] (initial base y) = final base y := by
  have hc := copy_run base [] y
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hc
  have he : y.length+3 = (y.length+1)+1+1 := by omega
  rw [he,Function.iterate_succ_apply,start_step,Function.iterate_succ_apply,mark_step,
    Function.iterate_succ_apply',hc,copy_done]
