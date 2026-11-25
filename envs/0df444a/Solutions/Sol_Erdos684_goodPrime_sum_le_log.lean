-- Prove2me | solution 1 for Erdos684.goodPrime_sum_le_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:48:34.533314+00:00
-- url     : https://prove2.me/submissions/52a54a19-495c-465b-8b49-f1be443495ea

module
public import Definitions.Def_Erdos684_Finite
public import Definitions.Def_Erdos684_BadPrimes
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Definitions.Def_Erdos684_Averaging
public import Theorems.Thm_Erdos684_log_smallPrimePart


set_option autoImplicit false
@[expose] public section
public section
open Finset Real
open Erdos684
namespace Erdos684
theorem _root_.solution (n X A k : ℕ) :
    ∑ p ∈ goodPrimes n X A, primeWeight n k p ≤ log (smallPrimePart n k : ℝ) := by
  classical
  rw [log_smallPrimePart]
  have heq : ∑ p ∈ goodPrimes n X A, primeWeight n k p =
      ∑ p ∈ (goodPrimes n X A).filter (fun p => p ≤ k),
        ((n.choose k).factorization p : ℝ) * log p := by
    simp [primeWeight, Finset.sum_filter]
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpg, hpk⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpk, Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hpg).1⟩
  · intro p hp _
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le))
end Erdos684
