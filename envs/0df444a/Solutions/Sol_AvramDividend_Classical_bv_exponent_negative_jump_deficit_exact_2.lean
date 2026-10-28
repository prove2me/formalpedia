-- Prove2me | solution 2 for AvramDividend.Classical.bv_exponent_negative_jump_deficit_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T00:09:45.459915+00:00
-- url     : https://prove2.me/submissions/06c996de-9c4e-4e35-a2cc-88f60fed60b0

import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_positive_magnitude_exact
import Theorems.Thm_AvramDividend_Classical_negative_jump_magnitude_integral_transform
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (hBV : X.BoundedVariation)
    (θ : ℝ) (hθ : 1 ≤ θ) :
    X.drift * θ - X.ψ θ =
      ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν := by
  rw [bv_laplace_exponent_positive_magnitude_exact X hBV θ hθ]
  rw [negative_jump_magnitude_integral_transform]
  ring
