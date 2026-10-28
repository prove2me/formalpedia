-- Prove2me | solution 1 for BitDFT.header_setup_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:01:58.162066+00:00
-- url     : https://prove2.me/submissions/128733f4-9be6-4427-9c38-74d1a52c697f

import Definitions.Def_BitDFT_HeaderSetup
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction

namespace BitDFT.HeaderSetup
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

 theorem start_run (base : machine.Cfg) (src dim : List Bool) :
    machine.step (frame base .start src [] dim 0 (src.length+1) (dim.length+1)) =
      frame base .copy src [] dim 1 src.length (dim.length+1) := by
  let c := frame base .start src [] dim 0 (src.length+1) (dim.length+1)
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.copy,fun i => (c.cells i (c.head i),if i = 2 then Move.right else if i = 3 then Move.left else Move.stay)) := by
    apply Prod.ext
    · rfl
    · funext i
      change protect (c.cells i (c.head i)) (c.cells i (c.head i),_) = _
      apply protect_same
      fin_cases i <;> simp [c, frame, MultitapeTM.tapeOf]
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [c, frame]

theorem rewind2_step (base : machine.Cfg) (src dst dim : List Bool) (p h3 h4 : ℕ) :
    machine.step (frame base .rewind2 src dst dim (p+1) h3 h4) =
      frame base .rewind2 src dst dim p h3 h4 := by
  let c := frame base .rewind2 src dst dim (p+1) h3 h4
  have hn : c.cells 2 (c.head 2) ≠ TapeCopy.Sym.start := by
    exact positive_not_start dst (p+1) (by omega)
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.rewind2, fun i => (c.cells i (c.head i),if i = 2 then Move.left else Move.stay)) := by
    apply Prod.ext
    · change (raw .rewind2 (fun i => c.cells i (c.head i))).1 = _
      simp only [raw,hn,if_false]
    · funext i
      change protect (c.cells i (c.head i)) ((raw .rewind2 _).2 i) = _
      simp only [raw,hn,if_false]
      apply protect_same
      by_cases hi : i = 2
      · subst i; exact fun h => False.elim (hn h)
      · simp [hi]
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

theorem rewind2_run (base : machine.Cfg) (src dst dim : List Bool) (p h3 h4 : ℕ) :
    machine.step^[p] (frame base .rewind2 src dst dim p h3 h4) =
      frame base .rewind2 src dst dim 0 h3 h4 := by
  induction p with
  | zero => rfl
  | succ p ih => rw [Function.iterate_succ_apply,rewind2_step,ih]

theorem rewind4_step (base : machine.Cfg) (src dst dim : List Bool) (p h2 h3 : ℕ) :
    machine.step (frame base .rewind4 src dst dim h2 h3 (p+1)) =
      frame base .rewind4 src dst dim h2 h3 p := by
  let c := frame base .rewind4 src dst dim h2 h3 (p+1)
  have hn : c.cells 4 (c.head 4) ≠ TapeCopy.Sym.start := by
    exact positive_not_start dim (p+1) (by omega)
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.rewind4, fun i => (c.cells i (c.head i),if i = 4 then Move.left else Move.stay)) := by
    apply Prod.ext
    · change (raw .rewind4 (fun i => c.cells i (c.head i))).1 = _
      simp only [raw,hn,if_false]
    · funext i
      change protect (c.cells i (c.head i)) ((raw .rewind4 _).2 i) = _
      simp only [raw,hn,if_false]
      apply protect_same
      by_cases hi : i = 4
      · subst i; exact fun h => False.elim (hn h)
      · simp [hi]
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

theorem rewind4_run (base : machine.Cfg) (src dst dim : List Bool) (p h2 h3 : ℕ) :
    machine.step^[p] (frame base .rewind4 src dst dim h2 h3 p) =
      frame base .rewind4 src dst dim h2 h3 0 := by
  induction p with
  | zero => rfl
  | succ p ih => rw [Function.iterate_succ_apply,rewind4_step,ih]

theorem rewind4_done (base : machine.Cfg) (src dst dim : List Bool) :
    machine.step (frame base .rewind4 src dst dim 0 0 0) =
      frame base .halt src dst dim 1 1 1 := by
  let c := frame base .rewind4 src dst dim 0 0 0
  have hn : c.cells 4 (c.head 4) = TapeCopy.Sym.start := rfl
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.halt,fun i => (c.cells i (c.head i),if i = 2 ∨ i = 3 ∨ i = 4 then Move.right else Move.stay)) := by
    apply Prod.ext
    · change (raw .rewind4 (fun i => c.cells i (c.head i))).1 = _
      simp only [raw,hn,if_true]
    · funext i
      change protect (c.cells i (c.head i)) ((raw .rewind4 _).2 i) = _
      simp only [raw,hn,if_true]
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
    fin_cases i <;> simp [c,frame]

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

private theorem tape_erase (w : List Sym) (a : Sym) :
    Function.update (machine.tapeOf (w ++ [a])) (w.length + 1) .blank = machine.tapeOf w := by
  rw [← tape_append]
  rw [Function.update_idem]
  have he : machine.tapeOf w (w.length+1) = TapeCopy.Sym.blank := by
    simp [MultitapeTM.tapeOf]
  rw [← he]
  exact Function.update_eq_self _ _

theorem copy_step (base : machine.Cfg) (pre dst dim : List Bool) (b : Bool) (h4 : ℕ) :
    machine.step (frame base .copy (pre++[b]) dst dim (dst.length+1) (pre.length+1) h4) =
      frame base .copy pre (dst++[b]) dim (dst.length+2) pre.length h4 := by
  let c := frame base .copy (pre++[b]) dst dim (dst.length+1) (pre.length+1) h4
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.blank := by simp [c,frame,MultitapeTM.tapeOf]
  have h3 : c.cells 3 (c.head 3) = machine.bitSym b := by
    simp [c,frame,MultitapeTM.tapeOf,List.getD_append_right]
  have hb : c.cells 3 (c.head 3) = TapeCopy.Sym.zero ∨ c.cells 3 (c.head 3) = TapeCopy.Sym.one := by
    rw [h3]; cases b <;> simp [MultitapeTM.bitSym]
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.copy,fun i => (if i = 2 then machine.bitSym b else if i = 3 then TapeCopy.Sym.blank else c.cells i (c.head i),
        if i = 2 then Move.right else if i = 3 then Move.left else Move.stay)) := by
    apply Prod.ext
    · change (raw .copy (fun i => c.cells i (c.head i))).1 = _
      simp only [raw,hb,if_true]
    · funext i
      change protect (c.cells i (c.head i)) ((raw .copy _).2 i) = _
      simp only [raw,hb,if_true]
      fin_cases i
      · exact protect_same _ _ (by intro _; decide)
      · exact protect_same _ _ (by intro _; decide)
      · simp [h2,h3,protect,HeaderReader.protect]; cases b <;> simp [MultitapeTM.bitSym]
      · simp [h3,protect,HeaderReader.protect]; cases b <;> simp [MultitapeTM.bitSym]
      · exact protect_same _ _ (by intro _; decide)
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · simpa [c,frame,List.map_append] using tape_append (dst.map machine.bitSym) (machine.bitSym b)
    · simpa [c,frame,List.map_append] using tape_erase (pre.map machine.bitSym) (machine.bitSym b)
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [c,frame]

theorem copy_run (base : machine.Cfg) (src dst dim : List Bool) (h4 : ℕ) :
    machine.step^[src.length] (frame base .copy src dst dim (dst.length+1) src.length h4) =
      frame base .copy [] (dst++src.reverse) dim (dst.length+src.length+1) 0 h4 := by
  induction src using List.reverseRecOn generalizing dst with
  | nil => simp
  | append_singleton pre b ih =>
    simp only [List.length_append,List.length_singleton]
    rw [Function.iterate_succ_apply,copy_step]
    have h := ih (dst++[b])
    simpa [List.length_append,List.reverse_append,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem copy_done (base : machine.Cfg) (dst dim : List Bool) (h4 : ℕ) :
    machine.step (frame base .copy [] dst dim (dst.length+1) 0 h4) =
      frame base .rewind2 [] dst dim dst.length 0 h4 := by
  let c := frame base .copy [] dst dim (dst.length+1) 0 h4
  have hn : c.cells 3 (c.head 3) = TapeCopy.Sym.start := rfl
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.rewind2,fun i => (c.cells i (c.head i),if i = 2 then Move.left else Move.stay)) := by
    apply Prod.ext
    · change (raw .copy (fun i => c.cells i (c.head i))).1 = _
      simp only [raw,hn]; rfl
    · funext i
      change protect (c.cells i (c.head i)) ((raw .copy _).2 i) = _
      simp only [raw,hn]
      apply protect_same
      by_cases hi : i = 2
      · subst i
        have h := positive_not_start dst (dst.length+1) (by omega)
        exact fun h' => False.elim (h h')
      · simp [hi]
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

theorem rewind2_done (base : machine.Cfg) (dst dim : List Bool) :
    machine.step (frame base .rewind2 [] dst dim 0 0 (dim.length+1)) =
      frame base .rewind4 [] dst dim 0 0 dim.length := by
  let c := frame base .rewind2 [] dst dim 0 0 (dim.length+1)
  have hn : c.cells 2 (c.head 2) = TapeCopy.Sym.start := rfl
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.rewind4,fun i => (c.cells i (c.head i),if i = 4 then Move.left else Move.stay)) := by
    apply Prod.ext
    · change (raw .rewind2 (fun i => c.cells i (c.head i))).1 = _
      simp only [raw,hn,if_true]
    · funext i
      change protect (c.cells i (c.head i)) ((raw .rewind2 _).2 i) = _
      simp only [raw,hn,if_true]
      apply protect_same
      by_cases hi : i = 4
      · subst i
        have h := positive_not_start dim (dim.length+1) (by omega)
        exact fun h' => False.elim (h h')
      · simp [hi]
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

theorem setup_run (base : machine.Cfg) (src dim : List Bool) :
    machine.step^[2*src.length+dim.length+4]
      (frame base .start src [] dim 0 (src.length+1) (dim.length+1)) =
      frame base .halt [] src.reverse dim 1 1 1 := by
  let c := frame base .start src [] dim 0 (src.length+1) (dim.length+1)
  have hc : machine.step^[2*src.length+dim.length+4] c =
      machine.step^[1] (machine.step^[dim.length] (machine.step^[1]
        (machine.step^[src.length] (machine.step^[1] (machine.step^[src.length]
          (machine.step^[1] c)))))) := by
    simp only [← Function.iterate_add_apply]
    congr 1
    omega
  rw [hc]
  simp only [Function.iterate_one]
  have hcopy := copy_run base src [] dim (dim.length+1)
  simp only [List.length_nil,Nat.zero_add,List.nil_append] at hcopy
  rw [start_run,hcopy]
  rw [show src.length+1 = src.reverse.length+1 by simp,copy_done]
  rw [show src.length = src.reverse.length by simp,rewind2_run,rewind2_done,
      rewind4_run,rewind4_done]

end BitDFT.HeaderSetup

open BitDFT.HeaderSetup IntMul

theorem solution (base : machine.Cfg) (src dim : List Bool) :
    machine.step^[2*src.length+dim.length+4]
      (frame base .start src [] dim 0 (src.length+1) (dim.length+1)) =
      frame base .halt [] src.reverse dim 1 1 1 := by
  exact setup_run base src dim
