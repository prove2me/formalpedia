-- Prove2me | solution 1 for AvramDividend.Classical.bv_weighted_generator_residual_zero_of_transform_components
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:52:48.497709+00:00
-- url     : https://prove2.me/submissions/0763bd74-d9e8-4d93-8358-ccd44e0d2aed

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_rearrangement_of_integrable
import Theorems.Thm_AvramDividend_Classical_bv_scale_origin_drift_product_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The physical-drift boundary term cancels the scale-function Laplace denominator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hexp : IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1)
      (Iio (0 : ℝ)) X.ν)
    (hcomp : IntegrableOn
      (fun y : ℝ => θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
      (Iio (0 : ℝ)) X.ν)
    (hderiv : (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) * deriv W x) =
       θ * (X.ψ θ - q)⁻¹ - W 0)
    (hjump : (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) *
         (∫ y in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) =
       (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν) *
       (X.ψ θ - q)⁻¹ -
       θ * (X.c - X.drift) * (X.ψ θ - q)⁻¹ +
       (X.c - X.drift) * W 0)
    (hresidual : (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) *
         (X.generator W x - q * W x)) =
       X.c * (∫ x in Ioi (0 : ℝ),
         Real.exp (-(θ * x)) * deriv W x) +
       (∫ x in Ioi (0 : ℝ),
         Real.exp (-(θ * x)) *
           (∫ y in Iio (0 : ℝ),
              SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)) -
       q * (X.ψ θ - q)⁻¹) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) *
         (X.generator W x - q * W x)) = 0 := by
  have hψ := bv_laplace_exponent_rearrangement_of_integrable
    X hbv θ hexp hcomp
  have h0 : X.drift * W 0 = 1 :=
    bv_scale_origin_drift_product_one X hX hbv q hq W hW
  have hne : X.ψ θ - q ≠ 0 := sub_ne_zero.mpr (ne_of_gt hqθ)
  rw [hresidual, hderiv, hjump]
  calc
    X.c * (θ * (X.ψ θ - q)⁻¹ - W 0) +
        ((∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν) *
         (X.ψ θ - q)⁻¹ -
         θ * (X.c - X.drift) * (X.ψ θ - q)⁻¹ +
         (X.c - X.drift) * W 0) -
        q * (X.ψ θ - q)⁻¹
      = (X.drift * θ +
          (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν) -
          q) * (X.ψ θ - q)⁻¹ - X.drift * W 0 := by ring
    _ = 0 := by
      rw [h0]
      have hψalt : X.drift * θ +
          (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν) -
          q = X.ψ θ - q := by
        rw [hψ]
      rw [hψalt]
      simp [hne]
