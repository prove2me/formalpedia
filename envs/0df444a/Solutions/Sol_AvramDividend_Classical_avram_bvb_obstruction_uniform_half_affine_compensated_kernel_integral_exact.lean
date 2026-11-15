-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_uniform_half_affine_compensated_kernel_integral_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T01:02:40.434871+00:00
-- url     : https://prove2.me/submissions/17aeffb3-8b55-45e8-a583-a2ae10d7e23b

import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_compensated_kernel_interior_exact
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_compensated_kernel_exterior_zero
import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
theorem solution (y : ℝ) (hy : 0 < y) :
    (∫ z in Ioo (-1 : ℝ) 0,
      (if y + z < 0 then -(y + (1 / 2 : ℝ) + z) else 0)
        ∂(volume : Measure ℝ)) =
    if y < 1 then y * (y - 1) / 2 else 0 := by
  by_cases hlt : y < 1
  · simpa [hlt] using
      AvramDividend.Classical.avram_bvb_obstruction_uniform_compensated_kernel_interior_exact y hy hlt
  · have hge : 1 ≤ y := le_of_not_gt hlt
    simpa [hlt] using
      AvramDividend.Classical.avram_bvb_obstruction_uniform_compensated_kernel_exterior_zero y hge
