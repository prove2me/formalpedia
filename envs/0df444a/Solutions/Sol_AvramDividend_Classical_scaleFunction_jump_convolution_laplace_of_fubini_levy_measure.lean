-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_jump_convolution_laplace_of_fubini_levy_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:37:08.440006+00:00
-- url     : https://prove2.me/submissions/023e6a1d-6dcc-434f-a53d-8c7fafcbe890

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shifted_laplace_transform
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The negative-jump Levy measure stays fixed through the Laplace Fubini step. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hfubini :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)) =
      ∫ y in Iio (0 : ℝ),
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W (x + y)) ∂X.ν) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)) =
    (∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂X.ν) *
      (X.ψ θ - q)⁻¹ := by
  calc
    _ = ∫ y in Iio (0 : ℝ),
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * W (x + y)) ∂X.ν := hfubini
    _ = ∫ y in Iio (0 : ℝ),
      Real.exp (θ * y) * (X.ψ θ - q)⁻¹ ∂X.ν := by
        apply integral_congr_ae
        filter_upwards [(ae_restrict_mem (μ := X.ν) measurableSet_Iio)] with y hy
        exact scaleFunction_shifted_laplace_transform X q W hW θ y hθ hqθ
          (le_of_lt hy)
    _ = _ := integral_mul_const (X.ψ θ - q)⁻¹ _
