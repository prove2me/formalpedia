-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB280_translated_gaussian_inverse_sqrt_cell_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:46:31.585971+00:00
-- url     : https://prove2.me/submissions/b2678686-c38f-4cfa-b771-57044d1e3fea

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

private theorem baseTimeKernel (delta : ℝ) :
    ∫ x in (0 : ℝ)..delta, x ^ (-(1 / 2 : ℝ)) =
      2 * Real.sqrt delta := by
  have hr : (-1 : ℝ) < -(1 / 2 : ℝ) := by norm_num
  rw [integral_rpow (a := 0) (b := delta) (r := -(1 / 2 : ℝ)) (Or.inl hr)]
  have hzero : (0 : ℝ) ^ ((-(1 / 2 : ℝ)) + 1) = 0 := by
    norm_num
  rw [hzero]
  norm_num [Real.sqrt_eq_rpow]
  ring


theorem solution (s δ : ℝ) :
    ∫ t in s..(s + δ), (t - s) ^ (-(1 / 2 : ℝ)) =
      2 * Real.sqrt δ := by
  rw [intervalIntegral.integral_comp_sub_right
    (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) s]
  simpa only [sub_self, add_sub_cancel_left] using baseTimeKernel δ
