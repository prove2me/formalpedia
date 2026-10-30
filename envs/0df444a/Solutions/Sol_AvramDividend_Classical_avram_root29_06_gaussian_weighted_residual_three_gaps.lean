-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_06_gaussian_weighted_residual_three_gaps
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:20:47.099009+00:00
-- url     : https://prove2.me/submissions/8c92c958-662d-4f10-acbc-6080ef2512ba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_weighted_generator_residual_zero_of_fubini_right_slope
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline
import Theorems.Thm_AvramDividend_Classical_exp_compensated_jump_integrable_levy
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_gaussian_scale_generator_origin_normalization_from_right_limit

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (θ η : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hDlim : Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 η))
    (hderiv1 : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (deriv W) (deriv (deriv W) x) x)
    (hD2int : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv (deriv W) x) (Ioi (0 : ℝ)))
    (hJint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν))
      (Ioi (0 : ℝ)))
    (hfubini :
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) *
          (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
      ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) *
            SpectrallyNegativeLevy.generatorIntegrand W x y) ∂X.ν) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      ((X.σ ^ 2 / 2) * deriv (deriv W) x + X.c * deriv W x +
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν) -
        q * W x)) = 0 := by
  have hk := exp_compensated_jump_integrable_levy X θ hθ
  refine scaleFunction_global_weighted_generator_residual_zero_of_fubini_right_slope X q W hW
    θ X.σ X.c η hθ hqθ ((hW.2.2.1 0 (Set.mem_Ici.mpr le_rfl)).mono_of_mem_nhdsWithin self_mem_nhdsWithin)
    hderiv hDlim hderiv1 ((hW.2.2.2.2 θ hθ hqθ).1)
    (AvramDividend.Classical.chat07_scale_weighted_deriv_integrable_positive_halfline X q W hW θ hθ hqθ)
    hD2int hJint
    (AvramDividend.Classical.scaleFunction_zero_origin_gaussian_without_standing X q hq W hW hσ)
    (gaussian_scale_generator_origin_normalization_from_right_limit X q hq W hW hσ η hDlim)
    (by simpa only [mul_assoc] using hk) hfubini ?_
  simp only [SpectrallyNegativeLevy.ψ, laplaceExponent, mul_assoc]
  rw [show ((fun _ : ℝ => (1:ℝ)) : ℝ → ℝ) = 1 from rfl]
  ring
