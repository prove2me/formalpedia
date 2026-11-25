-- Prove2me | solution 1 for Erdos684.goodPrimeWeight_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:10:20.063126+00:00
-- url     : https://prove2.me/submissions/3973a81a-597e-478d-8b3d-a343f1dfcf09

module
public import Definitions.Def_Erdos684_Finite
public import Definitions.Def_Erdos684_BadPrimes
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Definitions.Def_Erdos684_Averaging
public import Theorems.Thm_Erdos684_badPrimeWeight_le


set_option autoImplicit false
@[expose] public section
public section
open Finset Real
open Erdos684
namespace Erdos684
theorem _root_.solution (n X A : ℕ) (hn : 0 < n) :
    Chebyshev.theta X - A * log (n + A : ℕ) ≤
      ∑ p ∈ goodPrimes n X A, log p := by
  classical
  have hsplit : (∑ p ∈ goodPrimes n X A, log (p : ℝ)) +
      (∑ p ∈ badPrimes n X A, log (p : ℝ)) = Chebyshev.theta X := by
    rw [goodPrimes, badPrimes, Chebyshev.theta_eq_sum_primesLE_log,
      Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : A < p - n % p
    · simp [h, not_le.mpr h]
    · simp [h, Nat.le_of_not_gt h]
  have hb := badPrimeWeight_le n X A hn
  linarith
end Erdos684
