-- Prove2me | solution 1 for AvramDividend.Classical.bv_exponent_negative_jump_deficit_exact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:09:03.286895+00:00
-- url     : https://prove2.me/submissions/34c2d237-5f99-4061-8d9b-e754a4c9edfb

import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_positive_magnitude_exact
import Theorems.Thm_AvramDividend_Classical_negative_jump_magnitude_integral_transform
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The BV exponent deficit is exactly the negative-jump exponential integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (hBV : X.BoundedVariation)
    (θ : ℝ) (hθ : 1 ≤ θ) :
    X.drift * θ - X.ψ θ =
      ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν := by 
  rw [bv_laplace_exponent_positive_magnitude_exact X hBV θ hθ,
    negative_jump_magnitude_integral_transform]
  ring
