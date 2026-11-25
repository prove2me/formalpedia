-- Prove2me | solution 1 for Erdos684.averaged_smallPrimePart_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:17:36.940133+00:00
-- url     : https://prove2.me/submissions/08b0f964-45ce-444c-8b27-b449c06ed029

module
public import Definitions.Def_Erdos684_Finite
public import Definitions.Def_Erdos684_BadPrimes
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Definitions.Def_Erdos684_Averaging
public import Theorems.Thm_Erdos684_goodPrimeWeight_ge
public import Theorems.Thm_Erdos684_goodPrime_window_weight
public import Theorems.Thm_Erdos684_goodPrime_sum_le_log

set_option autoImplicit false
@[expose] public section
public section
open Finset Real
open Erdos684
namespace Erdos684
theorem _root_.solution (n X A : ℕ) (hn : 0 < n) (hX : 2 * X ≤ n) :
    (A : ℝ) * (Chebyshev.theta X - A * log (n + A : ℕ)) ≤
      ∑ k ∈ Finset.Icc 1 (2 * X), log (smallPrimePart n k : ℝ) := by
  calc
    (A : ℝ) * (Chebyshev.theta X - A * log (n + A : ℕ)) ≤
        A * ∑ p ∈ goodPrimes n X A, log (p : ℝ) :=
      mul_le_mul_of_nonneg_left (goodPrimeWeight_ge n X A hn) (Nat.cast_nonneg A)
    _ = ∑ p ∈ goodPrimes n X A, (A : ℝ) * log p := by rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ goodPrimes n X A, ∑ k ∈ Finset.Icc 1 (2 * X), primeWeight n k p :=
      Finset.sum_le_sum fun p hp => goodPrime_window_weight hX hp
    _ = ∑ k ∈ Finset.Icc 1 (2 * X), ∑ p ∈ goodPrimes n X A, primeWeight n k p := Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.Icc 1 (2 * X), log (smallPrimePart n k : ℝ) :=
      Finset.sum_le_sum fun k _ => goodPrime_sum_le_log n X A k
end Erdos684
