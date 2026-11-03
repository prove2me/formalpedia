-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_ae_cofinal_stopped_ito_terminal_payoff_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:37:14.113417+00:00
-- url     : https://prove2.me/submissions/a13d6424-a29c-47e7-a1fc-8f3a0ac3eb8e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ae_cofinal_random_clocks_expected_cash_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_any_measurable_clock_paid_cash_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Source stopped Ito estimates with nonnegative terminal payoffs exhaust original ruin cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : ℕ → Ω → ℝ≥0∞)
    (hσmeas : ∀ k : ℕ, Measurable (σ k))
    (hσmono : ∀ ω : Ω, Monotone (fun k : ℕ => σ k ω))
    (hSup : ∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω)
    (Terminal : ℕ → Ω → ℝ≥0∞) (budget : ℝ≥0∞)
    (hStopped : ∀ k : ℕ,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
        Terminal k ω) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  have hCash (k : ℕ) :
      (∫⁻ ω, (∫⁻ t in paymentTimes (σ k ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
    calc
      (∫⁻ ω, (∫⁻ t in paymentTimes (σ k ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤
          (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic T,
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
            Terminal k ω) ∂P) := by
        apply lintegral_mono
        intro ω
        calc
          (∫⁻ t in paymentTimes (σ k ω) ∩ Iic T,
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
              (∫⁻ t in paymentTimes (σ k ω) ∩ Iic T,
                ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) + 0 :=
              (add_zero _).symm
          _ ≤ _ := add_le_add_right (bot_le : (0 : ℝ≥0∞) ≤ Terminal k ω) _
      _ ≤ budget := hStopped k
  exact avram_wave7_19_original_ae_cofinal_random_clocks_expected_cash_budget
    X q x T D hD σ hσmono hSup
    (fun k => avram_wave7_19_original_any_measurable_clock_paid_cash_measurable
      D hD (σ k) (hσmeas k) q T)
    budget hCash
