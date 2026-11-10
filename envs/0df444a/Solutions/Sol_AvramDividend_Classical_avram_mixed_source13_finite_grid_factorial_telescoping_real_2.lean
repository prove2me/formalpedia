-- Prove2me | solution 2 for AvramDividend.Classical.avram_mixed_source13_finite_grid_factorial_telescoping_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:24:41.832204+00:00
-- url     : https://prove2.me/submissions/ca8a110b-60d4-4840-b3ba-003877e9a7ea

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open BigOperators
noncomputable section

/-- The factorial of a finite chronological count sum is its diagonal factorial
    contribution plus twice the sum over predecessor-current cell pairs. -/
theorem solution (k : ℕ) (a : ℕ → ℝ) :
    (∑ i ∈ Finset.range k, a i) * ((∑ i ∈ Finset.range k, a i) - 1) =
      (∑ i ∈ Finset.range k, a i * (a i - 1)) +
        2 * (∑ i ∈ Finset.range k, (∑ j ∈ Finset.range i, a j) * a i) := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [Finset.sum_range_succ]
      linear_combination ih
