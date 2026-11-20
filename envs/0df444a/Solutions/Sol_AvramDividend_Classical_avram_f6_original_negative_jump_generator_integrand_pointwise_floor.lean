-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_negative_jump_generator_integrand_pointwise_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:55:54.54179+00:00
-- url     : https://prove2.me/submissions/b2d22381-f67e-431a-a6f6-bb0af0bde9c9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (y z : ℝ)
    (hwpos : ∀ u : ℝ, 0 ≤ w u)
    (hd : 0 ≤ deriv w y) (hz : z < 0) :
    -w y ≤ SpectrallyNegativeLevy.generatorIntegrand w y z := by
  have hind : (0 : ℝ) ≤ (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) z := by
    by_cases hzi : z ∈ Ioo (-1 : ℝ) 1
    · simp [Set.indicator, hzi]
    · simp [Set.indicator, hzi]
  have hnonneg : 0 ≤ -(deriv w y) * z *
      (Ioo (-1 : ℝ) 1).indicator 1 z := by
    have ha : 0 ≤ -(deriv w y) * z :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hd) hz.le
    exact mul_nonneg ha hind
  unfold SpectrallyNegativeLevy.generatorIntegrand
  nlinarith [hwpos (y + z)]
