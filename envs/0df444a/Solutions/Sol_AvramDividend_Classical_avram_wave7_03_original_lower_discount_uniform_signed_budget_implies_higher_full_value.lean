-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_lower_discount_uniform_signed_budget_implies_higher_full_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:38:44.578929+00:00
-- url     : https://prove2.me/submissions/94aea250-4cc4-4774-b482-cc39b4bbd189

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_expected_signed_horizon_antitone_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Genuine lower-rate signed Stieltjes budgets transfer through every
    original horizon to the complete higher-rate ENNReal dividend value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂) (B : ℝ)
    (hfinite : ∀ n : ℕ, ∀ᵐ ω ∂P, (dividendMeasure D ω)
      (paymentTimes (ruinTime X x D ω) ∩ Iic (((n + 1 : ℕ) : ℝ))) ≠ ⊤)
    (hInt₁ : ∀ n : ℕ, Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q₁ * t)) ∂(dividendMeasure D ω)) P)
    (hInt₂ : ∀ n : ℕ, Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q₂ * t)) ∂(dividendMeasure D ω)) P)
    (hBudget₁ : ∀ n : ℕ, (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((n + 1 : ℕ) : ℝ)),
      Real.exp (-(q₁ * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    dividendValue X q₂ x D ≤ ENNReal.ofReal B := by
  have hq₂ : 0 ≤ q₂ := le_trans hq₁ hq
  apply avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
    X x C D hD q₂ hq₂ B
  intro n
  exact (avram_wave7_03_original_expected_signed_horizon_antitone_discount
    X x D q₁ q₂ hq₁ hq (((n + 1 : ℕ) : ℝ))
    (hfinite n) (hInt₁ n) (hInt₂ n)).trans (hBudget₁ n)
