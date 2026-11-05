-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_finite_clock_postpayment_branch_iff_zero_or_horizon_precedes_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T01:03:03.813035+00:00
-- url     : https://prove2.me/submissions/82b30699-22c8-4bc7-aca5-7ea989de51ec

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

/-- For the original controlled reserve and finite ruin-truncated clock,
the postpayment source branch is exactly the zero-clock or pre-ruin horizon
branch, including zero ruin and equality at the horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω, (τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) ↔
      (τ ω = 0 ∨ (n : ℝ≥0∞) < ruinTime X x D ω) := by
  have hτexact :=
    avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
      X x D n τ hτeq
  intro ω
  constructor
  · rintro (hzero | hshort)
    · exact Or.inl hzero
    · by_cases hbefore : (n : ℝ≥0∞) < ruinTime X x D ω
      · exact Or.inr hbefore
      · exfalso
        have hrn : ruinTime X x D ω ≤ (n : ℝ≥0∞) :=
          le_of_not_gt hbefore
        have hm : min (ruinTime X x D ω) (n : ℝ≥0∞) <
            ruinTime X x D ω := by
          simpa [hτexact ω] using hshort
        exact (lt_irrefl (ruinTime X x D ω))
          (by simpa [min_eq_left hrn] using hm)
  · rintro (hzero | hbefore)
    · exact Or.inl hzero
    · right
      rw [hτexact ω, min_eq_right (le_of_lt hbefore)]
      exact hbefore
