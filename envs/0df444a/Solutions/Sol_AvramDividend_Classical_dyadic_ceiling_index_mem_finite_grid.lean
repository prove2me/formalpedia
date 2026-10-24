-- Prove2me | solution 1 for AvramDividend.Classical.dyadic_ceiling_index_mem_finite_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T20:49:46.915348+00:00
-- url     : https://prove2.me/submissions/60b40c33-c28b-4a90-9a23-914007bbc817

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Range
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_rounding_bounds
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-- A bounded time has a dyadic ceiling index inside the explicit finite grid. -/
theorem solution
    (t T : ℝ≥0) (ht : t ≤ T) (n : ℕ) :
    Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) ∈
      Finset.range (Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n) + 1) := by
  rw [Finset.mem_range]
  have hreal : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
  have hscale : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hm :
      (t : ℝ) * (2 : ℝ) ^ n ≤ (T : ℝ) * (2 : ℝ) ^ n :=
    mul_le_mul_of_nonneg_right hreal hscale
  exact Nat.lt_succ_of_le (Nat.ceil_mono hm)