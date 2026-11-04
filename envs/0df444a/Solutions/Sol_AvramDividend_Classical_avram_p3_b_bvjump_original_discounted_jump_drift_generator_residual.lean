-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_discounted_jump_drift_generator_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:08:28.384764+00:00
-- url     : https://prove2.me/submissions/b51068db-0233-44f7-8301-75176dc40e1e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_jump_drift_eq_generator_sub_physical_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Discounting the original BV jump-compensator drift preserves the exact
physical generator convention at the source pre-jump reserve. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (u q t : ℝ) (hGen : X.GeneratorIntegrable w u) :
    (∫ z in Iio (0 : ℝ),
      Real.exp (-(q * t)) * (w (u + z) - w u) ∂X.ν) =
      Real.exp (-(q * t)) *
        (X.generator w u - X.drift * deriv w u) := by
  rw [integral_const_mul]
  rw [avram_p3_b_bvjump_original_jump_drift_eq_generator_sub_physical_drift
    X hBV w u hGen]
