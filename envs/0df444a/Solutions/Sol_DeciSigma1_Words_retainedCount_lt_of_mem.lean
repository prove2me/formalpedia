-- Prove2me | solution 1 for DeciSigma1.Words.retainedCount_lt_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:44:29.84288+00:00
-- url     : https://prove2.me/submissions/4f245f61-4b35-4422-ab69-80f9cddbb0f0

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_retainedCount_succ_of_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_add_le
public import Theorems.Thm_DeciSigma1_Words_retainedCount_le

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution {p a : ℕ} (hp : p ∈ D) (hpa : p < a) : retainedCount D a < a := by
  have h1 := retainedCount_succ_of_mem hp
  have h2 := retainedCount_le (D := D) p
  have h3 := retainedCount_add_le (D := D) (p + 1) (a - (p + 1))
  rw [show p + 1 + (a - (p + 1)) = a by omega] at h3
  omega
end DeciSigma1.Words
