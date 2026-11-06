-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_strict_positive_terminal_budget_to_every_nat_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:55:38.734074+00:00
-- url     : https://prove2.me/submissions/bd7f5ddf-dc02-491e-9af2-a4b2cb25b6fc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_real_stopped_cash_le_closed_horizon_cash
import Theorems.Thm_AvramDividend_Classical_avram_limit2_strict_later_real_horizon_cash_dominates_closed
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (B : ℝ≥0∞)
    (Terminal : ℝ → Ω → ℝ≥0∞)
    (hPositive : ∀ (T : ℝ), 0 < T →
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal T ω) ∂P) ≤ B) :
    ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B := by
  intro n
  have hn : (0 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hLater : (n : ℝ) < (n : ℝ) + 1 := by linarith
  have hPositiveLater : 0 < (n : ℝ) + 1 := by linarith
  have hCast : ENNReal.ofReal (n : ℝ) = (n : ℝ≥0∞) := by simp
  have hBound :
      (∫⁻ ω, ∫⁻ t in paymentTimes
        (min (ruinTime X x D ω) (ENNReal.ofReal (n : ℝ))),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B := by
    calc
      _ ≤ (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) :=
        avram_limit2_original_real_stopped_cash_le_closed_horizon_cash
          X q x D (n : ℝ) hn
      _ ≤ (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Set.Iio ((n : ℝ) + 1),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) :=
        avram_limit2_strict_later_real_horizon_cash_dominates_closed
          X q x D (n : ℝ) ((n : ℝ) + 1) hLater
      _ ≤ (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Set.Iio ((n : ℝ) + 1),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ((n : ℝ) + 1) ω) ∂P) := by
        apply lintegral_mono
        intro ω
        exact le_add_of_nonneg_right bot_le
      _ ≤ B := hPositive ((n : ℝ) + 1) hPositiveLater
  simpa only [hCast] using hBound
