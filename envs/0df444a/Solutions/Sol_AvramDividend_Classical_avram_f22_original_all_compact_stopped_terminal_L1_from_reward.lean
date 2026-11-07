-- Prove2me | solution 1 for AvramDividend.Classical.avram_f22_original_all_compact_stopped_terminal_L1_from_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:36:51.156001+00:00
-- url     : https://prove2.me/submissions/e272c75d-0403-45ad-b95a-42848551d378

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f21_original_earlier_clock_terminal_L1_from_exact_payoff
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hCashτI : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P)
    (σ : ℕ → Ω → ℝ≥0)
    (hStop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hBound : ∀ k ω, σ k ω ≤ τ ω)
    (Term F : ℕ → Ω → ℝ)
    (hExact : ∀ k ω, F k ω = Term k ω +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P) :
    ∀ k, Integrable (Term k) P := by
  intro k
  exact avram_f21_original_earlier_clock_terminal_L1_from_exact_payoff
    X x q hq C D hD (σ k) τ (hBound k)
    (avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
      (σ k) (hStop k)) hCashτI (Term k) (F k)
    (hExact k) (hFI k)
