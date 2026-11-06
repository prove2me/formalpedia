-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_cofinal_closed_terminal_budget_real_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:21:39.727198+00:00
-- url     : https://prove2.me/submissions/a780a443-2838-4cc3-b443-742ecc25892b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_arbitrary_cofinal_closed_horizon_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_perpetual_real_cash_mean_le_of_value_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Original closed cofinal cash plus nonnegative terminal budgets bound
    perpetual real Stieltjes payout and its genuine expected mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (T : ℕ → ℝ) (hT : ∀ a : ℝ, ∃ k : ℕ, a ≤ T k)
    (B : ℝ) (hB : 0 ≤ B)
    (hBudget : ∀ k : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T k),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤
        ENNReal.ofReal B) :
    dividendValue X q x D ≤ ENNReal.ofReal B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal (∫ ω,
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B := by
  have hValue : dividendValue X q x D ≤ ENNReal.ofReal B := by
    rw [avram_limit2_arbitrary_cofinal_closed_horizon_exhaustion X q x D hD T hT]
    apply iSup_le
    intro k
    obtain ⟨Terminal, hTerminal⟩ := hBudget k
    calc
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T k),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T k),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) := by
        apply lintegral_mono
        intro ω
        exact le_add_of_nonneg_right bot_le
      _ ≤ ENNReal.ofReal B := hTerminal
  have hFinite : dividendValue X q x D < ⊤ :=
    lt_of_le_of_lt hValue ENNReal.ofReal_lt_top
  obtain ⟨hL1, hExact⟩ :=
    avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
      X x D hD.1 q hFinite
  obtain ⟨_, hMean⟩ :=
    avram_limit2_original_perpetual_real_cash_mean_le_of_value_bound
      X x D hD.1 q B hB hValue
  exact ⟨hValue, hL1, hExact, hMean⟩
