-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_bounded_random_clock_toReal_budget_to_ennreal_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:38:41.370428+00:00
-- url     : https://prove2.me/submissions/cf99e672-17d8-4f27-a805-3406f0a52f2b

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_toReal_cash_mean_eq_signed_stieltjes_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Exact original stopped ENNReal cash bound from the real expectation
    of the same random-clock ENNReal pathwise cash converted by toReal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (B : ℝ)
    (hBudget :
      (∫ ω, (∫⁻ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by
  have hEq :=
    avram_wave7_03_original_bounded_random_clock_toReal_cash_mean_eq_signed_stieltjes_mean
      X x C D hD q hq T τ hτBound hτMeas
  rw [hEq] at hBudget
  rw [avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
    X x C D hD q hq T τ hτBound hτMeas]
  exact ENNReal.ofReal_le_ofReal hBudget
