-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_terminal_switch_right_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:31:44.215732+00:00
-- url     : https://prove2.me/submissions/cb397e10-8f11-486c-8429-ffe0c2677eca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postsource_rightpayment_reserve_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Exact canonical stopped-terminal convention: active stops take the right-payment reserve, and ruin-time stops do not. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, W ω = riskProcess X x D (τ ω) ω -
      (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
       then rightLimit D (τ ω) ω - D (τ ω) ω
       else 0) := by
  intro ω
  rw [hW ω]
  by_cases ha : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
  · simp only [if_pos ha]
    exact avram_p4_d_dividend_postsource_rightpayment_reserve_eq
      X x D ω (τ ω)
  · simp only [if_neg ha, sub_zero]