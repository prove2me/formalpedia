-- Prove2me | solution 1 for AvramDividend.Classical.chat07_scale_shift_weighted_signed_integral_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:29:08.576461+00:00
-- url     : https://prove2.me/submissions/bef1a797-0a32-4fe2-b3cc-1b2fcf683037

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_chat07_scale_shift_weighted_abs_integral_exact
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A negative scale increment is the negative of its absolute increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (r : ℝ) (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ*x)) * (W (x-r) - W x)) =
      (Real.exp (-(θ*r)) - 1) * (X.ψ θ - q)⁻¹ := by
  have hm : Monotone W := scaleFunction_monotone X q W hW
  have h := chat07_scale_shift_weighted_abs_integral_exact
    X q W hW θ hθ hqθ r hr
  calc
    (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ*x)) * (W (x-r) - W x)) =
        -(∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ*x)) * |W x - W (x-r)|) := by
          rw [← MeasureTheory.integral_neg]
          congr 1
          ext x
          rw [abs_of_nonneg (sub_nonneg.mpr
            (hm (sub_le_self x (le_of_lt hr))))]
          ring
    _ = (Real.exp (-(θ*r)) - 1) * (X.ψ θ - q)⁻¹ := by
      rw [h]
      ring
