-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_true_clock_stopped_integrand_eventually_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:32:52.067206+00:00
-- url     : https://prove2.me/submissions/a1d9e22f-cd32-4658-890c-cc514de7650d

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_clock_eventually_strict_preruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Every original ruin-truncated stopped integrand stabilises pointwise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (f : ℝ≥0 → ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (if (t : ℝ≥0∞) < min (ruinTime X x D ω) (n : ℝ≥0∞)
        then f t else 0) =
      (if (t : ℝ≥0∞) < ruinTime X x D ω then f t else 0) := by
  by_cases hRuin : (t : ℝ≥0∞) < ruinTime X x D ω
  · have hEventually :=
      avram_p4_e_localise_original_true_clock_eventually_strict_preruin
        X x C D hD ω t hRuin
    filter_upwards [hEventually] with n hn
    simp [hRuin, hn]
  · apply Filter.Eventually.of_forall
    intro n
    have hn : ¬ (t : ℝ≥0∞) <
        min (ruinTime X x D ω) (n : ℝ≥0∞) := by
      intro h
      exact hRuin (lt_of_lt_of_le h (min_le_left _ _))
    simp [hRuin, hn]
