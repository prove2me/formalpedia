-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB262_gaussian_small_ball_inverse_sqrt_time_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:40:53.364573+00:00
-- url     : https://prove2.me/submissions/f195fb88-ecb7-4426-9e42-69d1d018b5e9

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

theorem solution (delta : ℝ) :
    ∫ x in (0 : ℝ)..delta, x ^ (-(1 / 2 : ℝ)) =
      2 * Real.sqrt delta := by
  have hr : (-1 : ℝ) < -(1 / 2 : ℝ) := by norm_num
  rw [integral_rpow (a := 0) (b := delta) (r := -(1 / 2 : ℝ)) (Or.inl hr)]
  have hzero : (0 : ℝ) ^ ((-(1 / 2 : ℝ)) + 1) = 0 := by
    norm_num
  rw [hzero]
  norm_num [Real.sqrt_eq_rpow]
  ring
