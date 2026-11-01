-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_jump_laplace_of_product_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:20:20.92518+00:00
-- url     : https://prove2.me/submissions/7554c70b-1d84-43fa-ad78-3513acf9a6f7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_signed_weighted_product_integrable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_weighted_global_fubini_of_prod_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_compensated_fixed_jump_laplace

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- Exact original source primitive integrated jump Laplace transform via genuine Fubini. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 < θ) (hqθ : q < X.ψ θ) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x y ∂X.ν)) =
      (∫ y in Iio (0 : ℝ),
        Real.exp (θ * y) - 1 -
          θ * (y * (Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y) ∂X.ν) *
        ((X.ψ θ - q)⁻¹ / θ) := by
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  have hprod :=
    avram_wave4_p2_unbounded_scale_primitive_signed_weighted_product_integrable
      X hX hnbv q hq W hW θ hθ hqθ
  have hfubini :=
    scaleFunction_generator_weighted_global_fubini_of_prod_integrable X U θ hprod
  change (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
    (∫ y in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand U x y ∂X.ν)) = _
  rw [hfubini]
  have hpoint :
      (∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
          SpectrallyNegativeLevy.generatorIntegrand U x y) ∂X.ν) =
      ∫ y in Iio (0 : ℝ),
        ((Real.exp (θ * y) - 1 -
          θ * (y * (Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y)) *
          ((X.ψ θ - q)⁻¹ / θ)) ∂X.ν := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := X.ν) measurableSet_Iio] with y hy
    exact avram_wave4_p2_unbounded_scale_primitive_compensated_fixed_jump_laplace
      X hnbv q hq W hW θ y hθ hqθ hy.le
  rw [hpoint, MeasureTheory.integral_mul_const]
