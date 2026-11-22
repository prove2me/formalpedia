-- Prove2me | solution 1 for DeciSigma1.Words.retainedCount_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:50:04.947805+00:00
-- url     : https://prove2.me/submissions/336644a8-20e6-411c-92b8-1124a4e16853

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_retainedCount_succ

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (a n : ℕ) : retainedCount D (a + n) ≤ retainedCount D a + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc, retainedCount_succ]
    split_ifs <;> omega
end DeciSigma1.Words
