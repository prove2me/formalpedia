-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_jump_convolution_fubini_of_prod_integrable_levy_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:46:23.003302+00:00
-- url     : https://prove2.me/submissions/12595a95-58da-4f83-b6f4-95d28b2c7aa3

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
import Mathlib.MeasureTheory.Integral.Prod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Lévy-measure weighted jump convolution Fubini under product integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (θ : ℝ)
    (hint : Integrable (Function.uncurry
      (fun x y : ℝ => Real.exp (-(θ * x)) * W (x + y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ))))) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)) =
    ∫ y in Iio (0 : ℝ),
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W (x + y)) ∂X.ν := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let ν : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  haveI : SFinite ν := levy_negative_jump_measure_sFinite X
  change (∫ x, Real.exp (-(θ * x)) * (∫ y, W (x + y) ∂ν) ∂μ) =
    ∫ y, (∫ x, Real.exp (-(θ * x)) * W (x + y) ∂μ) ∂ν
  calc
    (∫ x, Real.exp (-(θ * x)) * (∫ y, W (x + y) ∂ν) ∂μ) =
        ∫ x, (∫ y, Real.exp (-(θ * x)) * W (x + y) ∂ν) ∂μ := by
          congr 1
          funext x
          rw [integral_const_mul]
    _ = ∫ y, (∫ x, Real.exp (-(θ * x)) * W (x + y) ∂μ) ∂ν :=
      integral_integral_swap hint
