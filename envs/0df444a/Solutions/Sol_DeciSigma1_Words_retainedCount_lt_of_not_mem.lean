-- Prove2me | solution 1 for DeciSigma1.Words.retainedCount_lt_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:49:24.516473+00:00
-- url     : https://prove2.me/submissions/200d9256-1fa3-4c29-a513-2efab38c212d

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_retainedCount_succ_of_not_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_mono

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution {a b : ℕ} (h : a ∉ D) (hab : a < b) :
    retainedCount D a < retainedCount D b := by
  have := retainedCount_succ_of_not_mem h
  have := retainedCount_mono (D := D) (show a + 1 ≤ b by omega)
  omega
end DeciSigma1.Words
