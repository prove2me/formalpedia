-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_dyadic_slope_tendstoInMeasure_zero_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:16:32.658997+00:00
-- url     : https://prove2.me/submissions/9c43145e-1424-468d-9d96-8784b62ede00

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Theorems.Thm_AvramDividend_Classical_bv_actual_dyadic_deficit_tendstoInMeasure_zero_ws01c

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hBV : X.BoundedVariation) :
    TendstoInMeasure P
      (fun (n : ℕ) (ω : Ω) =>
        X.drift -
          (X.X (((2 : ℝ≥0)⁻¹) ^ n) ω - X.X 0 ω) /
            ((((2 : ℝ≥0)⁻¹) ^ n : ℝ≥0) : ℝ))
      atTop (fun _ => (0 : ℝ)) := by
  refine (bv_actual_dyadic_deficit_tendstoInMeasure_zero_ws01c X hBV).congr_left
    (fun n => Filter.Eventually.of_forall fun ω => ?_)
  simp only [X.X_zero, sub_zero, NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat]
  have h2 : (0:ℝ) < 2 ^ n := by positivity
  rw [inv_pow]
  field_simp
