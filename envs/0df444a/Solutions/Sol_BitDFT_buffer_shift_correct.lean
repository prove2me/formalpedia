-- Prove2me | solution 1 for BitDFT.buffer_shift_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T17:02:33.613109+00:00
-- url     : https://prove2.me/submissions/2c434bef-e429-4ce2-a9f2-727a7f1047eb

import Definitions.Def_BitDFT_BufferShift
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases

namespace BitDFT.BufferShift
open IntMul
private def moveHead (p : ℕ) : Move → ℕ
  | .left => p-1
  | .stay => p
  | .right => p+1
private theorem cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem protect_same (a : Sym) (d : Move)
    (h : a = .start → d ≠ .left) : protect a (a,d) = (a,d) := by
  by_cases ha : a = .start
  · simp [protect, HeaderReader.protect, ha, h ha]
  · simp [protect, HeaderReader.protect, ha]

private theorem frame_step (base : machine.Cfg) (q q' : State) (w w' : List Sym)
    (p p' : ℕ) (a : Sym) (d : Move)
    (ht : transition q (fun i => (frame base q w p).cells i ((frame base q w p).head i)) =
      (q', fun i => if i = 1 then (a,d) else (base.cells i (base.head i),Move.stay)))
    (hw : Function.update (machine.tapeOf w) p a = machine.tapeOf w')
    (hp : moveHead p d = p') :
    machine.step (frame base q w p) = frame base q' w' p' := by
  apply cfg_ext
  · simpa only [MultitapeTM.step,frame] using congrArg Prod.fst ht
  · change (fun i => Function.update ((frame base q w p).cells i) ((frame base q w p).head i)
      ((transition q _).2 i).1) = _
    rw [ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact hw
  · change (fun i => moveHead ((frame base q w p).head i) ((transition q _).2 i).2) = _
    rw [ht]
    funext i
    fin_cases i
    · rfl
    · exact hp

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


private theorem tape_replace (pre post : List Sym) (a b : Sym) :
    Function.update (machine.tapeOf (pre++a::post)) (pre.length+1) b =
      machine.tapeOf (pre++b::post) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    by_cases hp : p = pre.length
    · subst p; simp [MultitapeTM.tapeOf]
    · rw [Function.update_of_ne (by omega : p+1 ≠ pre.length+1)]
      simp only [MultitapeTM.tapeOf]
      by_cases hlt : p < pre.length
      · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hlt]
      · have hge : pre.length ≤ p := by omega
        rw [List.getD_append_right _ _ _ _ hge,List.getD_append_right _ _ _ _ hge]
        have hn : p-pre.length ≠ 0 := by omega
        cases he : p-pre.length with
        | zero => exact False.elim (hn he)
        | succ k => rfl

theorem read_bit (base : machine.Cfg) (pre post : List Bool) (b : Bool) (gap : Sym) :
    machine.step (buffer base .read (pre++[b]) gap post (pre.length+1)) =
      buffer base (.write b) (pre++[b]) gap post (pre.length+2) := by
  let w := (pre++[b]).map machine.bitSym ++ [gap] ++ post.map machine.bitSym ++ [TapeCopy.Sym.sep]
  have hr : machine.tapeOf w (pre.length+1) = machine.bitSym b := by
    simp [w,MultitapeTM.tapeOf,List.map_append,List.append_assoc]
  apply frame_step base .read (.write b) w w (pre.length+1) (pre.length+2) (machine.bitSym b) .right
  · apply Prod.ext
    · simp [transition,raw,frame,hr]; cases b <;> rfl
    · funext i
      fin_cases i
      · change protect (base.cells 0 (base.head 0)) ((raw .read _).2 0) = _
        cases b <;> simp [raw,frame,hr,MultitapeTM.bitSym,protect_same]
      · change protect (machine.tapeOf w (pre.length+1)) ((raw .read _).2 1) = _
        cases b <;> simp [raw,frame,hr,MultitapeTM.bitSym,protect,HeaderReader.protect]
  · rw [← hr]; exact Function.update_eq_self _ _
  · rfl


theorem write_bit (base : machine.Cfg) (pre post : List Bool) (b : Bool) (gap : Sym)
    (hg : gap ≠ .start) :
    machine.step (buffer base (.write b) (pre++[b]) gap post (pre.length+2)) =
      buffer base .back pre (machine.bitSym b) (b::post) (pre.length+1) := by
  let w := (pre++[b]).map machine.bitSym ++ [gap] ++ post.map machine.bitSym ++ [TapeCopy.Sym.sep]
  let w' := pre.map machine.bitSym ++ [machine.bitSym b] ++ (b::post).map machine.bitSym ++ [TapeCopy.Sym.sep]
  have hr : machine.tapeOf w (pre.length+2) = gap := by
    have he : pre.length+2 = (pre++[b]).length+1 := by simp
    rw [he]; simp [w,MultitapeTM.tapeOf,List.append_assoc]
  apply frame_step base (.write b) .back w w' (pre.length+2) (pre.length+1) (machine.bitSym b) .left
  · apply Prod.ext
    · rfl
    · funext i
      fin_cases i
      · exact protect_same _ .stay (by intro _; decide)
      · change protect (machine.tapeOf w (pre.length+2)) _ = _
        cases b <;> simp [raw,frame,hr,MultitapeTM.bitSym,protect,HeaderReader.protect,hg]
  · have h := tape_replace ((pre++[b]).map machine.bitSym) (post.map machine.bitSym++[TapeCopy.Sym.sep]) gap (machine.bitSym b)
    simpa [w,w',List.map_append,List.append_assoc] using h
  · simp [moveHead]

theorem back_step (base : machine.Cfg) (pre post : List Bool) (b : Bool) :
    machine.step (buffer base .back pre (machine.bitSym b) post (pre.length+1)) =
      buffer base .read pre (machine.bitSym b) post pre.length := by
  let w := pre.map machine.bitSym ++ [machine.bitSym b] ++ post.map machine.bitSym ++ [TapeCopy.Sym.sep]
  have hr : machine.tapeOf w (pre.length+1) = machine.bitSym b := by
    simp [w,MultitapeTM.tapeOf,List.append_assoc]
  apply frame_step base .back .read w w (pre.length+1) pre.length (machine.bitSym b) .left
  · apply Prod.ext
    · rfl
    · funext i
      fin_cases i
      · exact protect_same _ .stay (by intro _; decide)
      · change protect (machine.tapeOf w (pre.length+1)) _ = _
        cases b <;> simp [raw,frame,hr,MultitapeTM.bitSym,protect,HeaderReader.protect]
  · rw [← hr]; exact Function.update_eq_self _ _
  · simp [moveHead]

theorem bit_cycle (base : machine.Cfg) (pre post : List Bool) (b : Bool) (gap : Sym)
    (hg : gap ≠ .start) :
    machine.step^[3] (buffer base .read (pre++[b]) gap post (pre.length+1)) =
      buffer base .read pre (machine.bitSym b) (b::post) pre.length := by
  change machine.step (machine.step (machine.step _)) = _
  rw [read_bit,write_bit base pre post b gap hg,back_step]


theorem read_marker (base : machine.Cfg) (w : List Sym) :
    machine.step (frame base .read w 0) = frame base .gap w 1 := by
  apply frame_step base .read .gap w w 0 1 .start .right
  · apply Prod.ext
    · simp [transition,raw,frame,MultitapeTM.tapeOf]
    · funext i
      fin_cases i
      · change protect (base.cells 0 (base.head 0)) _ = _
        simp [raw,frame,MultitapeTM.tapeOf,protect_same]
      · simp [transition,raw,frame,MultitapeTM.tapeOf,protect,HeaderReader.protect]
  · change Function.update (machine.tapeOf w) 0 (machine.tapeOf w 0) = _
    exact Function.update_eq_self _ _
  · rfl

theorem erase_gap (base : machine.Cfg) (gap : Sym) (w : List Sym) (hg : gap ≠ .start) :
    machine.step (frame base .gap (gap::w) 1) = frame base .halt (.blank::w) 1 := by
  apply frame_step base .gap .halt (gap::w) (.blank::w) 1 1 .blank .stay
  · apply Prod.ext
    · rfl
    · funext i
      fin_cases i
      · exact protect_same _ .stay (by intro _; decide)
      · simp [transition,raw,frame,MultitapeTM.tapeOf,protect,HeaderReader.protect,hg]
  · exact tape_replace [] w gap .blank
  · rfl

theorem finish_run (base : machine.Cfg) (pre post : List Bool) (gap : Sym) (hg : gap ≠ .start) :
    machine.step^[3*pre.length+2] (buffer base .read pre gap post pre.length) =
      frame base .halt ([.blank]++(pre++post).map machine.bitSym++[.sep]) 1 := by
  induction pre using List.reverseRecOn generalizing post gap with
  | nil =>
    simp only [List.length_nil,Nat.mul_zero,Nat.zero_add,buffer,List.map_nil,List.nil_append,List.singleton_append]
    rw [show (2:ℕ) = 1+1 from rfl,Function.iterate_add_apply]
    simp only [Function.iterate_one]
    rw [read_marker]
    simpa only [List.cons_append] using erase_gap base gap (post.map machine.bitSym++[.sep]) hg
  | append_singleton pre b ih =>
    have he : 3*(pre++[b]).length+2 = (3*pre.length+2)+3 := by simp; omega
    rw [he,Function.iterate_add_apply]
    have hc := bit_cycle base pre post b gap hg
    simp only [List.length_append,List.length_singleton] at *
    rw [hc,ih (b::post) (machine.bitSym b) (by cases b <;> decide)]
    simp [List.append_assoc]

private theorem tape_blank (w : List Sym) : machine.tapeOf (w++[.blank]) = machine.tapeOf w := by
  rw [← tape_append]
  have hr : machine.tapeOf w (w.length+1) = TapeCopy.Sym.blank := by simp [MultitapeTM.tapeOf]
  rw [← hr]; exact Function.update_eq_self _ _

theorem start_step (base : machine.Cfg) (w : List Sym) (p : ℕ) :
    machine.step (frame base .start w p) = frame base .separator w (p+1) := by
  apply frame_step base .start .separator w w p (p+1) (machine.tapeOf w p) .right
  · apply Prod.ext
    · rfl
    · funext i
      fin_cases i
      · exact protect_same _ .stay (by intro _; decide)
      · exact protect_same _ .right (by intro _; decide)
  · exact Function.update_eq_self _ _
  · rfl

theorem separator_step (base : machine.Cfg) (w : List Sym) :
    machine.step (frame base .separator w (w.length+2)) =
      frame base .left (w++[TapeCopy.Sym.blank,TapeCopy.Sym.sep]) (w.length+1) := by
  apply frame_step base .separator .left w (w++[TapeCopy.Sym.blank,TapeCopy.Sym.sep]) (w.length+2) (w.length+1) .sep .left
  · apply Prod.ext
    · rfl
    · funext i
      fin_cases i
      · exact protect_same _ .stay (by intro _; decide)
      · simp [transition,raw,frame,MultitapeTM.tapeOf, List.getD_eq_default,protect,HeaderReader.protect]
  · have h := tape_append (w++[TapeCopy.Sym.blank]) TapeCopy.Sym.sep
    rw [tape_blank] at h
    simpa [List.append_assoc,Nat.add_assoc] using h
  · simp [moveHead]

theorem left_step (base : machine.Cfg) (w : List Sym) :
    machine.step (frame base .left (w++[TapeCopy.Sym.blank,TapeCopy.Sym.sep]) (w.length+1)) =
      frame base .read (w++[TapeCopy.Sym.blank,TapeCopy.Sym.sep]) w.length := by
  have hr : machine.tapeOf (w++[TapeCopy.Sym.blank,TapeCopy.Sym.sep]) (w.length+1) = TapeCopy.Sym.blank := by
    simp [MultitapeTM.tapeOf]
  apply frame_step base .left .read (w++[TapeCopy.Sym.blank,TapeCopy.Sym.sep]) (w++[TapeCopy.Sym.blank,TapeCopy.Sym.sep]) (w.length+1) w.length .blank .left
  · apply Prod.ext
    · rfl
    · funext i
      fin_cases i
      · exact protect_same _ .stay (by intro _; decide)
      · simp [transition,raw,frame,hr,protect,HeaderReader.protect]
  · simpa only [hr] using Function.update_eq_self (w.length+1) (machine.tapeOf (w++[TapeCopy.Sym.blank,TapeCopy.Sym.sep]))
  · simp [moveHead]

theorem setup (base : machine.Cfg) (w : List Bool) :
    machine.step^[3] (frame base .start (w.map machine.bitSym) (w.length+1)) =
      buffer base .read w .blank [] w.length := by
  change machine.step (machine.step (machine.step _)) = _
  rw [start_step]
  have hl : w.length+1+1 = (w.map machine.bitSym).length+2 := by simp [Nat.add_assoc]
  rw [hl,separator_step,left_step]
  simp [buffer,List.append_assoc]

end BitDFT.BufferShift

open BitDFT.BufferShift IntMul

theorem solution (base : machine.Cfg) (w : List Bool) :
    machine.step^[3*w.length+5] (frame base .start (w.map machine.bitSym) (w.length+1)) =
      frame base .halt ([TapeCopy.Sym.blank]++w.map machine.bitSym++[TapeCopy.Sym.sep]) 1 := by
  rw [show 3*w.length+5 = (3*w.length+2)+3 by omega, Function.iterate_add_apply,setup]
  simpa using finish_run base w [] .blank (by decide)
