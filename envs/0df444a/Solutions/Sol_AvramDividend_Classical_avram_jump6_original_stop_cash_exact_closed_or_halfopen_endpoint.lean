-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_original_stop_cash_exact_closed_or_halfopen_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T19:07:34.85098+00:00
-- url     : https://prove2.me/submissions/62814eee-aa6e-419b-be9b-bb352873762d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_ruin_horizon_paymentTimes_eq_Ico
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact canonical stopped dividend cash domain includes the terminal
payment at a strict pre-ruin clock and excludes it at positive ruin contact. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (τ : Ω → ℝ≥0)
    (hRuinBound : (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
    paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ) =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then Icc (0 : ℝ) (τ ω : ℝ)
      else Ico (0 : ℝ) (τ ω : ℝ) := by
  by_cases hPre : τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
  · simpa only [if_pos hPre] using
      (avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
        X x D ω τ hPre)
  · have hτne : τ ω ≠ 0 := by
      intro hZero
      exact hPre (Or.inl hZero)
    have hτpos : 0 < τ ω :=
      lt_of_le_of_ne (show (0 : ℝ≥0) ≤ τ ω from zero_le) (Ne.symm hτne)
    have hNotLt :
        ¬ (τ ω : ℝ≥0∞) < ruinTime X x D ω := by
      intro h
      exact hPre (Or.inr h)
    have hEq : ruinTime X x D ω = (τ ω : ℝ≥0∞) :=
      le_antisymm (le_of_not_gt hNotLt) hRuinBound
    simp only [if_neg hPre]
    rw [hEq]
    exact avram_wave8_21_original_ruin_horizon_paymentTimes_eq_Ico
      (τ ω) hτpos

