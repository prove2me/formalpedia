-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_uniform_compensated_kernel_exterior_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T01:02:21.465314+00:00
-- url     : https://prove2.me/submissions/0ddec1aa-f68b-43e5-af2d-a9cb6cf7641e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
theorem solution (y : ℝ) (hy : 1 ≤ y) :
    (∫ z in Ioo (-1 : ℝ) 0,
      (if y + z < 0 then -(y + (1 / 2 : ℝ) + z) else 0)
        ∂(volume : Measure ℝ)) = (0 : ℝ) := by
  have hNo : ∀ z ∈ Ioo (-1 : ℝ) 0, ¬ y + z < 0 := by
    intro z hz
    have hLeft : (-1 : ℝ) < z := hz.1
    linarith
  calc
    _ = (∫ z in Ioo (-1 : ℝ) 0, (0 : ℝ)
      ∂(volume : Measure ℝ)) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro z hz
        simp [hNo z hz]
    _ = 0 := by simp
