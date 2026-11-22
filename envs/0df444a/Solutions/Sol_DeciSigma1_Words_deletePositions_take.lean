-- Prove2me | solution 1 for DeciSigma1.Words.deletePositions_take
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:47:43.094161+00:00
-- url     : https://prove2.me/submissions/3e76d7ea-478e-4253-a3a0-bf48397b99e2

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_deletePositions_append
public import Theorems.Thm_DeciSigma1_Words_length_deletePositions

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (w : List α) {a : ℕ} (ha : a ≤ w.length) :
    (deletePositions w D).take (retainedCount D a) = deletePositions (w.take a) D := by
  conv_lhs => rw [← List.take_append_drop a w, deletePositions_append]
  rw [List.take_left' (by rw [length_deletePositions, List.length_take, min_eq_left ha])]
end DeciSigma1.Words
