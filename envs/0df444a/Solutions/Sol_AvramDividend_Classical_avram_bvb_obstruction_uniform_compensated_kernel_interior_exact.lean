-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_uniform_compensated_kernel_interior_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T01:02:30.797563+00:00
-- url     : https://prove2.me/submissions/85e6fcd8-9653-4f6e-a5cf-421f939227ad

import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_kernel_crossing_indicator_set_integral
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_affine_truncated_interval_integral_exact
import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
theorem solution (y : ℝ) (hy : 0 < y) (hy1 : y < 1) :
    (∫ z in Ioo (-1 : ℝ) 0,
      (if y + z < 0 then -(y + (1 / 2 : ℝ) + z) else 0)
        ∂(volume : Measure ℝ)) = y * (y - 1) / 2 := by
  have hbelow : (-1 : ℝ) ≤ -y := by linarith
  rw [AvramDividend.Classical.avram_bvb_obstruction_uniform_kernel_crossing_indicator_set_integral y hy hy1]
  rw [← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le hbelow]
  exact AvramDividend.Classical.avram_bvb_obstruction_uniform_affine_truncated_interval_integral_exact y
