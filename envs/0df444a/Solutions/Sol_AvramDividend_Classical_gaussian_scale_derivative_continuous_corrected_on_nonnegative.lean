-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_scale_derivative_continuous_corrected_on_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:05:38.008078+00:00
-- url     : https://prove2.me/submissions/7a101cee-eb14-4c90-aff6-825677e595ce

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_gaussian_scale_derivative_right_continuous_extension
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The Gaussian derivative extends continuously to zero by the right slope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ContinuousOn (fun x : ℝ => if x = 0 then 2 / X.σ ^ 2 else deriv W x)
      (Ici (0 : ℝ)) := by
  have hzero : W 0 = 0 :=
    scaleFunction_zero_origin_gaussian_without_standing X q hq W hW hσ
  have hC1 := scaleFunction_contDiff_one_gaussian_without_standing
    X q hq W hW hσ
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt W (deriv W x) x := by
    intro x hx
    exact ((hC1.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt
      (by norm_num)).hasDerivAt
  exact gaussian_scale_derivative_right_continuous_extension
    X q hq W hW hσ hzero hderiv
