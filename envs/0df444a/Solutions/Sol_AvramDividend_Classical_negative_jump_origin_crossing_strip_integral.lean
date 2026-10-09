-- Prove2me | solution 1 for AvramDividend.Classical.negative_jump_origin_crossing_strip_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:19:11.45097+00:00
-- url     : https://prove2.me/submissions/efd0e3ec-7c7a-4fa0-a295-a749f0a49d8d

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (y : ℝ) (hy : y < 0) :
    (∫ x in Ioo (0 : ℝ) (-y), (-y)) = y ^ 2 := by
  have hlen : (0 : ℝ) ≤ -y := le_of_lt (neg_pos.mpr hy)
  calc
    (∫ x in Ioo (0 : ℝ) (-y), (-y)) =
        (volume.real (Ioo (0 : ℝ) (-y))) * (-y) := by
          simp only [setIntegral_const, smul_eq_mul]
    _ = y ^ 2 := by
      rw [Real.volume_real_Ioo_of_le hlen]
      ring
