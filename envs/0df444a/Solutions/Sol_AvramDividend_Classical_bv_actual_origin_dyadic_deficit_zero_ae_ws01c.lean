-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_origin_dyadic_deficit_zero_ae_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:39:50.790655+00:00
-- url     : https://prove2.me/submissions/ea235c81-adb5-4d75-a8cd-64074ff26702

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_origin_dyadic_cauchy_ae_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_actual_dyadic_slope_tendstoInMeasure_zero_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_ae_cauchy_plus_in_measure_bundle_ws01c

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        X.drift -
          (X.X (((1 : ℝ≥0) / 2) ^ n) ω - X.X 0 ω) /
            (((1 : ℝ≥0) / 2) ^ n : ℝ))
        atTop (𝓝 (0 : ℝ)) := by
  have hC := bv_actual_origin_dyadic_cauchy_ae_ws01c X hBV
  have hM := bv_actual_dyadic_slope_tendstoInMeasure_zero_ws01c X hBV
  push_cast at hC hM ⊢
  simp only [one_div] at hC hM ⊢
  exact bv_ae_cauchy_plus_in_measure_bundle_ws01c P _ hC hM
