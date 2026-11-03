-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_uniform_signed_budgets_give_perpetual_L1_real_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:51:44.748525+00:00
-- url     : https://prove2.me/submissions/047d8fba-3719-49f1-a8cf-3ed1c65603f5

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_finite_iff_uniform_signed_horizon_mean_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_cash_toReal_L1_and_exact_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- A short genuine original-measure consumer: uniform real signed
    horizon budgets supply L1 perpetual cash and its exact real mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (B : ℝ)
    (hBudget : ∀ n : ℕ,
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω : Ω,
          (∫⁻ t in paymentTimes (ruinTime X x D ω),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) := by
  have hFinite : dividendValue X q x D < ⊤ :=
    (avram_wave7_03_original_dividendValue_finite_iff_uniform_signed_horizon_mean_bounded
      X x C D hD q hq).2 ⟨B, hBudget⟩
  exact avram_wave7_03_original_perpetual_cash_toReal_L1_and_exact_mean
    X x D hD.1.1 q hFinite
