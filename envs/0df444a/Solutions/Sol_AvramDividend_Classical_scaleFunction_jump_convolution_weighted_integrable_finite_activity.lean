-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_jump_convolution_weighted_integrable_finite_activity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:20:59.537782+00:00
-- url     : https://prove2.me/submissions/27f48267-1b2d-41eb-8019-24da0ce20e00

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_product_integrable_finite_activity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Integrate the weighted finite-activity jump convolution in reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν))
      (Ioi (0 : ℝ)) volume := by
  letI : IsFiniteMeasure (X.ν.restrict (Iio (0 : ℝ))) :=
    ⟨by simpa using hFinite⟩
  have hprod := scaleFunction_jump_convolution_product_integrable_finite_activity
    X q W hW θ hθ hqθ hFinite
  have hinner := hprod.integral_prod_left
  simpa only [IntegrableOn, Function.uncurry_apply_pair, integral_const_mul] using hinner
