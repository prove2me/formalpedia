-- Prove2me | solution 1 for DeciSigma1.Words.retainedCount_add_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:54:37.29548+00:00
-- url     : https://prove2.me/submissions/ddc5fa8f-8c51-4160-8545-6d6290559f71

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_retainedCount_succ_of_mem

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution {a n : ℕ} (h : ∀ i < n, a + i ∈ D) :
    retainedCount D (a + n) = retainedCount D a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc, retainedCount_succ_of_mem (h n (by omega)),
        ih (fun i hi => h i (by omega))]
end DeciSigma1.Words
