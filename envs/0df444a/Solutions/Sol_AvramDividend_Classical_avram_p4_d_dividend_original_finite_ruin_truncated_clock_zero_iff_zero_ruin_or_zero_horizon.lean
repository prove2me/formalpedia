-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_finite_ruin_truncated_clock_zero_iff_zero_ruin_or_zero_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T01:03:43.835708+00:00
-- url     : https://prove2.me/submissions/be2dbd42-6b65-42e4-b871-e7d1ce963668

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The source clock is zero exactly when the controlled reserve ruins at
zero or the selected finite observation horizon is itself zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω, (τ ω : ℝ≥0∞) = 0 ↔
      ruinTime X x D ω = 0 ∨ n = 0 := by
  have hτexact :=
    avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
      X x D n τ hτeq
  intro ω
  rw [hτexact ω]
  constructor
  · intro hzero
    by_cases hrn : ruinTime X x D ω ≤ (n : ℝ≥0∞)
    · left
      simpa [min_eq_left hrn] using hzero
    · right
      have hnr : (n : ℝ≥0∞) ≤ ruinTime X x D ω :=
        le_of_not_ge hrn
      have hnzero : (n : ℝ≥0∞) = 0 := by
        simpa [min_eq_right hnr] using hzero
      simpa using hnzero
  · rintro (hrzero | hnzero)
    · simp [hrzero]
    · simp [hnzero]
