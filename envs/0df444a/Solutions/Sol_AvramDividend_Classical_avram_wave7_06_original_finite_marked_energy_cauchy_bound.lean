-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_finite_marked_energy_cauchy_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:09:56.559195+00:00
-- url     : https://prove2.me/submissions/91c31269-d76a-49e3-95de-5e9f33d689b8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-- Finite-energy Cauchy bound for the actual source marked-jump times. -/
theorem solution
    (F : Finset ℝ≥0) (H : ℝ≥0 → ℝ) :
    (∑ u ∈ F, H u) ^ 2 ≤
      (F.card : ℝ) * (∑ u ∈ F, (H u) ^ 2) := by
  simpa using (sq_sum_le_card_mul_sum_sq (s := F) (f := H))
