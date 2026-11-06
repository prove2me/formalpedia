-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_natural_stopped_terminal_real_perpetual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T09:59:13.096208+00:00
-- url     : https://prove2.me/submissions/33e86880-f884-4aee-acfc-518c2045cea0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_perpetual_real_cash_mean_le_of_value_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Uniform natural ruin-stopped original cash-plus-terminal budgets imply
    a finite perpetual value and its exact real signed Stieltjes mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (B : ℝ) (hB : 0 ≤ B)
    (Terminal : ℕ → Ω → ℝ≥0∞)
    (hStopped : ∀ n : ℕ,
      (∫⁻ ω, ((∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) + Terminal n ω) ∂P)
      ≤ ENNReal.ofReal B) :
    dividendValue X q x D ≤ ENNReal.ofReal B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B := by
  have hCash : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by
    intro n
    calc
      _ ≤ (∫⁻ ω, ((∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) + Terminal n ω) ∂P) := by
        apply lintegral_mono
        intro ω
        exact le_add_of_nonneg_right bot_le
      _ ≤ ENNReal.ofReal B := hStopped n
  have hValue :
      dividendValue X q x D ≤ ENNReal.ofReal B :=
    avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
      X q x D hD (ENNReal.ofReal B) hCash
  have hFinite : dividendValue X q x D < ⊤ :=
    lt_of_le_of_lt hValue ENNReal.ofReal_lt_top
  obtain ⟨hRealL1, hExact⟩ :=
    avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
      X x D hD.1 q hFinite
  obtain ⟨_, hMean⟩ :=
    avram_limit2_original_perpetual_real_cash_mean_le_of_value_bound
      X x D hD.1 q B hB hValue
  exact ⟨hValue, hRealL1, hExact, hMean⟩
