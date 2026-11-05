-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_finite_ruin_clock_equals_horizon_or_ruin_on_matching_physical_branches
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T01:06:16.011973+00:00
-- url     : https://prove2.me/submissions/b03fd027-2fac-4ca8-aefd-ad0ee560ee17

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

/-- The actual controlled reserve reaches either the finite horizon or
ruin first; equality at the horizon satisfies both physical clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω,
      ((n : ℝ≥0∞) ≤ ruinTime X x D ω →
        (τ ω : ℝ≥0∞) = (n : ℝ≥0∞)) ∧
      (ruinTime X x D ω ≤ (n : ℝ≥0∞) →
        (τ ω : ℝ≥0∞) = ruinTime X x D ω) := by
  have hτexact :=
    avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
      X x D n τ hτeq
  intro ω
  constructor
  · intro hbefore
    rw [hτexact ω]
    exact min_eq_right hbefore
  · intro hruin
    rw [hτexact ω]
    exact min_eq_left hruin
