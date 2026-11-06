-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_closed_cash_plus_nonnegative_terminal_to_all_nat_stops
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:48:36.908545+00:00
-- url     : https://prove2.me/submissions/6c27ec56-5347-4a00-ac20-b2e3da27859b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_real_stopped_cash_le_closed_horizon_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (B : ℝ≥0∞)
    (Terminal : ℝ → Ω → ℝ≥0∞)
    (hBudget : ∀ (T : ℝ) (hT : 0 ≤ T),
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal T ω) ∂P) ≤ B) :
    ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B := by
  intro n
  have hn : (0 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hCast : ENNReal.ofReal (n : ℝ) = (n : ℝ≥0∞) := by
    simp
  have hBound :
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal (n : ℝ))),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B := by
    calc
      _ ≤ (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) :=
        avram_limit2_original_real_stopped_cash_le_closed_horizon_cash X q x D (n : ℝ) hn
      _ ≤ (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal (n : ℝ) ω) ∂P) := by
        apply lintegral_mono
        intro ω
        exact le_add_of_nonneg_right bot_le
      _ ≤ B := hBudget (n : ℝ) hn
  simpa only [hCast] using hBound
