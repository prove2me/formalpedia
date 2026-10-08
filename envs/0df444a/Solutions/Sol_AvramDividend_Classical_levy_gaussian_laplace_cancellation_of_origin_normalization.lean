-- Prove2me | solution 1 for AvramDividend.Classical.levy_gaussian_laplace_cancellation_of_origin_normalization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:30:21.999802+00:00
-- url     : https://prove2.me/submissions/fe560c39-469e-4662-95df-70a32075b70e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_generator_laplace_cancellation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q θ η : ℝ) (hqθ : q < X.ψ θ)
    (horigin : (X.σ ^ 2 / 2) * η = 1) :
    ((X.σ ^ 2 / 2) * θ ^ 2 + X.c * θ +
      (∫ y in Iio (0 : ℝ),
        (Real.exp (θ * y) - 1 -
          θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂X.ν) - q) *
      (X.ψ θ - q)⁻¹ - (X.σ ^ 2 / 2) * η = 0 := by
  let J : ℝ :=
    ∫ y in Iio (0 : ℝ),
      (Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂X.ν
  have hψ :
      X.ψ θ = (X.σ ^ 2 / 2) * θ ^ 2 + X.c * θ + J := by
    dsimp [SpectrallyNegativeLevy.ψ, laplaceExponent, J]
    ring
  exact gaussian_generator_laplace_cancellation
    (X.σ ^ 2 / 2) X.c θ q (X.ψ θ) J η hψ hqθ horigin
