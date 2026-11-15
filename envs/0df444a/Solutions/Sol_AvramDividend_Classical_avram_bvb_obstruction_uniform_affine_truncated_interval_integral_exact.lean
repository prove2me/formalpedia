-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_uniform_affine_truncated_interval_integral_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:52:53.798482+00:00
-- url     : https://prove2.me/submissions/e195a26f-fb0f-49fa-8166-438edfe06b30

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory intervalIntegral Real
theorem solution (y : ℝ) :
    (∫ z in (-1 : ℝ)..(-y), -(y + (1 / 2 : ℝ) + z)) =
      y * (y - 1) / 2 := by
  have h : (fun z : ℝ => -(y + (1 / 2 : ℝ) + z)) =
      (fun z => -(y + (1 / 2 : ℝ)) - z) := by
    funext z
    ring
  have hc : IntervalIntegrable
      (fun _ : ℝ => -(y + (1 / 2 : ℝ)))
      volume (-1) (-y) := continuous_const.intervalIntegrable _ _
  have hi : IntervalIntegrable (fun z : ℝ => z)
      volume (-1) (-y) := continuous_id.intervalIntegrable _ _
  rw [h, intervalIntegral.integral_sub hc hi]
  simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
  ring
