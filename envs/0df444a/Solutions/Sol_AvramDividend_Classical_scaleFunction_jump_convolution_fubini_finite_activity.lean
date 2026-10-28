-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_jump_convolution_fubini_finite_activity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:49:54.561135+00:00
-- url     : https://prove2.me/submissions/49e56fcf-c6a5-4076-84d6-4bb6a794b2e9

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Finite jump activity supplies the measure instance needed by Fubini. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (θ : ℝ)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hint : Integrable (Function.uncurry
      (fun x y : ℝ => Real.exp (-(θ * x)) * W (x + y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ))))) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)) =
    ∫ y in Iio (0 : ℝ),
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W (x + y)) ∂X.ν := by
  letI : IsFiniteMeasure (X.ν.restrict (Iio (0 : ℝ))) := by
    refine ⟨?_⟩
    simpa using hFinite
  calc
    _ = ∫ x in Ioi (0 : ℝ),
          (∫ y in Iio (0 : ℝ),
            Real.exp (-(θ * x)) * W (x + y) ∂X.ν) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact (integral_const_mul (Real.exp (-(θ * x)))
            (fun y : ℝ => W (x + y))).symm
    _ = _ := integral_integral_swap hint
