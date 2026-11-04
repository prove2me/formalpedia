-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_levy_weighted_lintegral_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:52:20.349675+00:00
-- url     : https://prove2.me/submissions/8ee0863d-279b-4d4d-a61f-d5d9bb04dd63

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_levy_weighted_moment_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ρ θ : ℝ) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ) :
    (∫⁻ y in Iio (0 : ℝ), ENNReal.ofReal
      (Real.exp (ρ * y) * (Real.exp (θ * y) - 1) ^ 4) ∂X.ν) < ⊤ := by
  have hi :=
    AvramDividend.Classical.avram_p2_b_rate_original_levy_weighted_moment_integrable
      X ρ θ hρ hθ
  have hn : ∀ᵐ y ∂X.ν.restrict (Iio (0 : ℝ)),
      0 ≤ Real.exp (ρ * y) * (Real.exp (θ * y) - 1) ^ 4 :=
    Filter.Eventually.of_forall (fun y => by positivity)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hi hn]
  exact ENNReal.ofReal_lt_top
