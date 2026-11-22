-- Prove2me | solution 1 for DeciSigma1.Words.retainedCount_succ_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:48:46.718522+00:00
-- url     : https://prove2.me/submissions/614cc858-1d95-47df-9e06-0b9e7bc0cb0f

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
theorem _root_.solution {a : ℕ} (h : a ∉ D) :
    retainedCount D (a + 1) = retainedCount D a + 1 := by
  rw [retainedCount_succ, if_neg h]
end DeciSigma1.Words
