-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_uniform_signed_budgets_imply_signed_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:46:19.747759+00:00
-- url     : https://prove2.me/submissions/b092e647-1b66-4ed6-b21c-2ea478510212

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_direct_uniform_signed_budget_to_ennreal
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_signed_stieltjes_L1_of_full_ennreal_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Uniform original signed budgets for finite-clock truncations
    imply L1 of the true full original signed Stieltjes reward at τ. -/
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
    (hBudget : ∀ n : ℕ,
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩
          Iic ((min (τ ω) (((n + 1 : ℕ) : ℝ≥0)) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P := by
  have hCashBudget :=
    avram_wave7_03_original_finite_random_clock_direct_uniform_signed_budget_to_ennreal
      X x C D hD q hq τ hτMeas B hBudget
  have hCashFinite :
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) < ⊤ :=
    lt_of_le_of_lt hCashBudget ENNReal.ofReal_lt_top
  exact
    avram_wave7_03_original_finite_random_clock_signed_stieltjes_L1_of_full_ennreal_finite
      X x C D hD q hq τ hτMeas hCashFinite
