-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_strict_survival_terminal_expectation_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:18:42.787126+00:00
-- url     : https://prove2.me/submissions/f75ecace-7c6e-4ed3-b7d4-91abf53f6236

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exactly killed terminal expectations are nonnegative, without a budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (H : ℝ≥0) :
    0 ≤ ∫ ω, (if (H : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (H : ℝ))) *
        w (x + X.X H ω - rightLimit D H ω))
      else 0) ∂P := by
  apply integral_nonneg
  intro ω
  by_cases hS : (H : ℝ≥0∞) < ruinTime X x D ω
  · simpa only [Pi.zero_apply, if_pos hS] using
      (le_max_left (0 : ℝ)
        (Real.exp (-(q * (H : ℝ))) *
          w (x + X.X H ω - rightLimit D H ω)))
  · simp only [Pi.zero_apply, if_neg hS, le_refl]
