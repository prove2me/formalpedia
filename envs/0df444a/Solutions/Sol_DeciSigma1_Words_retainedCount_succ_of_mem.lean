-- Prove2me | solution 1 for DeciSigma1.Words.retainedCount_succ_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:53:40.390588+00:00
-- url     : https://prove2.me/submissions/fb0e4fdd-c9e1-4c92-bcb2-db3c82b47d85

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
theorem _root_.solution {a : ℕ} (h : a ∈ D) :
    retainedCount D (a + 1) = retainedCount D a := by
  rw [retainedCount_succ, if_pos h, Nat.add_zero]
end DeciSigma1.Words
