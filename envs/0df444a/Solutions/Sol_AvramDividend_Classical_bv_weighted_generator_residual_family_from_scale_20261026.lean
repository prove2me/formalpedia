-- Prove2me | solution 1 for AvramDividend.Classical.bv_weighted_generator_residual_family_from_scale_20261026
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:44:24.985371+00:00
-- url     : https://prove2.me/submissions/e3f4278c-1e68-45d7-8e0d-f763c2bd4f96

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline
import Theorems.Thm_AvramDividend_Classical_bv_signed_generator_kernel_product_integrable
import Theorems.Thm_AvramDividend_Classical_bv_weighted_jump_integrable_of_product_integrable
import Theorems.Thm_AvramDividend_Classical_bv_scale_weighted_deriv_transform_of_boundary
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable_nonneg
import Theorems.Thm_AvramDividend_Classical_bv_truncated_negative_jump_integrable
import Theorems.Thm_AvramDividend_Classical_bv_truncated_jump_integral_eq_characteristic_drift_difference
import Theorems.Thm_AvramDividend_Classical_bv_weighted_jump_transform_from_fixed_jump_fubini
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_integral_decomposition
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_zero_of_transform_components
import Theorems.Thm_AvramDividend_Classical_bv_weighted_residual_integrable_from_scale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Assemble the entire BV q-scale generator residual transform. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) * (X.generator W x - q * W x))
        (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * (X.generator W x - q * W x)) = 0 := by
  intro θ hθ hqθ
  have hMon := scaleFunction_monotone X q W hW
  have hWint := (hW.2.2.2.2 θ hθ hqθ).1
  have hWlap := (hW.2.2.2.2 θ hθ hqθ).2
  have hDint :=
    chat07_scale_weighted_deriv_integrable_positive_halfline X q W hW θ hθ hqθ
  have hProd :=
    bv_signed_generator_kernel_product_integrable X hbv q W hW hMon θ hθ hqθ
  have hJint := bv_weighted_jump_integrable_of_product_integrable X θ W hProd
  have hCont : ContinuousWithinAt W (Ici (0 : ℝ)) 0 :=
    hW.2.2.1.continuousWithinAt (by simp)
  have hC1 := scaleFunction_contDiffOn_one_of_boundedVariation X hX q hq W hW hbv
  have hDer : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x := by
    intro x hx
    exact ((hC1.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt
      (by norm_num)).hasDerivAt
  have hD :=
    bv_scale_weighted_deriv_transform_of_boundary
      X q W hW θ hθ hqθ hCont hDer hWint hWlap
  have hExp := bv_exponential_jump_integrable_nonneg X hbv θ hθ
  have hK := bv_truncated_negative_jump_integrable X hbv
  have hKval := bv_truncated_jump_integral_eq_characteristic_drift_difference X hbv
  have hComp : IntegrableOn
      (fun y : ℝ => θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
      (Iio (0 : ℝ)) X.ν := by
    change Integrable
      (fun y : ℝ => θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
      (X.ν.restrict (Iio 0))
    convert hK.integrable.const_mul θ using 1
    funext y
    simp [mul_assoc]
    left
    left
    rfl
  have hJ :=
    bv_weighted_jump_transform_from_fixed_jump_fubini
      X q W hW θ hθ hqθ hCont hDer hDint hProd hExp hK hKval
  have hRdecomp :=
    bv_weighted_generator_residual_integral_decomposition
      X hbv q θ W hDint hJint hWint hWlap
  have hRint :=
    bv_weighted_residual_integrable_from_scale
      X hbv q W hW hMon θ hθ hqθ hWint
  refine ⟨hRint, ?_⟩
  exact bv_weighted_generator_residual_zero_of_transform_components
    X hX hbv q hq W hW θ hθ hqθ hExp hComp hD hJ hRdecomp
