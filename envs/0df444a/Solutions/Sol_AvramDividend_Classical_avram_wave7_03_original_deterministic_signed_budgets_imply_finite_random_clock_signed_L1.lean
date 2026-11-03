-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_deterministic_signed_budgets_imply_finite_random_clock_signed_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:59:17.649385+00:00
-- url     : https://prove2.me/submissions/73ee8b08-a9f5-45cf-854c-86cde04138de

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_deterministic_signed_budgets_imply_finite_random_clock_ennreal_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_signed_stieltjes_L1_of_full_ennreal_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original deterministic full Stieltjes real budgets imply the
    exact random-stopped original signed payout is P-integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (B : ℝ)
    (hDetBudget : ∀ n : ℕ,
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P := by
  have hBudget :=
    avram_wave7_03_original_deterministic_signed_budgets_imply_finite_random_clock_ennreal_budget
      X x C D hD q hq τ hτMeas B hDetBudget
  have hCashFinite :
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) < ⊤ :=
    lt_of_le_of_lt hBudget ENNReal.ofReal_lt_top
  exact
    avram_wave7_03_original_finite_random_clock_signed_stieltjes_L1_of_full_ennreal_finite
      X x C D hD q hq τ hτMeas hCashFinite
