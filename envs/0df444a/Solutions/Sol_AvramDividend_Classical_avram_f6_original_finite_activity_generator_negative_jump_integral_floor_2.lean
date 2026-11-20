-- Prove2me | solution 2 for AvramDividend.Classical.avram_f6_original_finite_activity_generator_negative_jump_integral_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:56:40.172495+00:00
-- url     : https://prove2.me/submissions/51c8c3f6-f51b-4398-9d5c-2caef0612e05

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_finite_jump_generator_lower
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal


noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hνFin : X.ν (Iio (0 : ℝ)) < ⊤)
    (w : ℝ → ℝ) (hwpos : ∀ u : ℝ, 0 ≤ w u)
    (y : ℝ) (hderiv : 0 ≤ deriv w y)
    (hGen : X.GeneratorIntegrable w y) :
    -(X.ν (Iio (0 : ℝ))).toReal * w y ≤
      ∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν  := by
  exact avram_mix_fin26_finite_jump_generator_lower
    X w y hνFin hGen
    (by intro t ht; exact hwpos t) hderiv
