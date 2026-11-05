-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:54:12.007292+00:00
-- url     : https://prove2.me/submissions/e1522d01-79f6-40a5-b9f5-6d9afa463ef6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At every original dividend path, truncating controlled ruin at the finite
integer horizon commutes exactly with the NNReal-to-ENNReal coercion. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω, (τ ω : ℝ≥0∞) =
      min (ruinTime X x D ω) (n : ℝ≥0∞) := by
  intro ω
  rw [hτeq ω]
  exact ENNReal.coe_toNNReal (by simp)
