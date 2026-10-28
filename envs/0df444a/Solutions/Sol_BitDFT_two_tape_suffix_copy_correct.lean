-- Prove2me | solution 1 for BitDFT.two_tape_suffix_copy_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:57:51.350765+00:00
-- url     : https://prove2.me/submissions/fa5a64e0-b6a3-4f8c-be04-0f2058af2ef8

import Definitions.Def_BitDFT_SuffixCopyTwoTape
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases

namespace BitDFT.SuffixCopyTwoTape
open IntMul

private theorem cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem protect_same (a : Sym) (d : Move)
    (h : a = .start → d ≠ .left) : protect a (a,d) = (a,d) := by
  by_cases ha : a = .start
  · simp [protect,HeaderReader.protect,ha,h ha]
  · simp [protect,HeaderReader.protect,ha]

private theorem tape_append (w : List Sym) (a : Sym) :
    Function.update (machine.tapeOf w) (w.length+1) a = machine.tapeOf (w++[a]) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    by_cases hp : p = w.length
    · subst p; simp [MultitapeTM.tapeOf,List.getD_append_right]
    · rw [Function.update_of_ne (by omega : p+1 ≠ w.length+1)]
      simp only [MultitapeTM.tapeOf]
      by_cases hlt : p < w.length
      · rw [List.getD_append _ _ _ _ hlt]
      · have hge : w.length ≤ p := by omega
        rw [List.getD_eq_default _ _ hge,List.getD_append_right _ _ _ _ hge]
        exact (List.getD_eq_default _ _ (by simp; omega)).symm

theorem copy_step (base : machine.Cfg) (pre : List Bool) (b : Bool) (rest out : List Bool) :
    machine.step (frame base .copy (pre++b::rest) out (pre.length+1)) =
      frame base .copy (pre++b::rest) (out++[b]) (pre.length+2) := by
  let c := frame base .copy (pre++b::rest) out (pre.length+1)
  have h0 : c.cells 0 (c.head 0) = machine.bitSym b := by
    simp [c,frame,MultitapeTM.tapeOf,List.append_assoc]
  have h1 : c.cells 1 (c.head 1) = TapeCopy.Sym.blank := by simp [c,frame,MultitapeTM.tapeOf]
  have hb : c.cells 0 (c.head 0) = TapeCopy.Sym.zero ∨ c.cells 0 (c.head 0) = TapeCopy.Sym.one := by
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
      · exact protect_same _ .right (by intro _; decide)
      · simp [h0,h1,protect,HeaderReader.protect]; cases b <;> simp [MultitapeTM.bitSym]
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · simpa [c,frame,List.map_append] using tape_append (out.map machine.bitSym) (machine.bitSym b)
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [c,frame]

theorem copy_run (base : machine.Cfg) (pre rest out : List Bool) :
    machine.step^[rest.length] (frame base .copy (pre++rest) out (pre.length+1)) =
      frame base .copy (pre++rest) (out++rest) (pre.length+rest.length+1) := by
  induction rest generalizing pre out with
  | nil => simp
  | cons b rest ih =>
    rw [List.length_cons,Function.iterate_succ_apply,copy_step]
    have h := ih (pre++[b]) (out++[b])
    simpa [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem copy_done (base : machine.Cfg) (input out : List Bool) :
    machine.step (frame base .copy input out (input.length+1)) =
      frame base .halt input out (input.length+1) := by
  let c := frame base .copy input out (input.length+1)
  have h0 : c.cells 0 (c.head 0) = TapeCopy.Sym.sep := by simp [c,frame,MultitapeTM.tapeOf]
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.halt,fun i => (c.cells i (c.head i),Move.stay)) := by
    apply Prod.ext
    · change (raw .copy (fun i => c.cells i (c.head i))).1 = _
      simp [raw,h0]
    · funext i
      change protect (c.cells i (c.head i)) ((raw .copy (fun j => c.cells j (c.head j))).2 i) = _
      simp only [raw,h0,reduceCtorEq,or_self,if_false]
      exact protect_same _ .stay (by intro _; decide)
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]; rfl

end BitDFT.SuffixCopyTwoTape
open BitDFT.SuffixCopyTwoTape IntMul

theorem solution (base : machine.Cfg) (pre rest out : List Bool) :
    machine.step^[rest.length+1] (frame base .copy (pre++rest) out (pre.length+1)) =
      frame base .halt (pre++rest) (out++rest) (pre.length+rest.length+1) := by
  rw [Function.iterate_succ_apply',copy_run]
  have h := copy_done base (pre++rest) (out++rest)
  simpa using h
