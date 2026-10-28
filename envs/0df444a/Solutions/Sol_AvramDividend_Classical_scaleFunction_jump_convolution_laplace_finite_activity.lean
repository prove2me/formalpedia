-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_jump_convolution_laplace_finite_activity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:04:43.444059+00:00
-- url     : https://prove2.me/submissions/7a803581-d234-4470-a842-f7a116923831

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_product_integrable_finite_activity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_fubini_finite_activity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_laplace_of_fubini_levy_measure
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The finite-activity weighted jump-convolution Laplace formula follows
    by product domination, Lévy-measure Fubini and shifted scale transform. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)) =
    (∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂X.ν) *
      (X.ψ θ - q)⁻¹ := by
  have hint :=
    scaleFunction_jump_convolution_product_integrable_finite_activity
      X q W hW θ hθ hqθ hFinite
  have hfubini :=
    scaleFunction_jump_convolution_fubini_finite_activity
      X W θ hFinite hint
  exact scaleFunction_jump_convolution_laplace_of_fubini_levy_measure
    X q W hW θ hθ hqθ hfubini
