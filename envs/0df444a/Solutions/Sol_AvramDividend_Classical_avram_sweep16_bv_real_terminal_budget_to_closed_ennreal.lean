-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_bv_real_terminal_budget_to_closed_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:21:17.629627+00:00
-- url     : https://prove2.me/submissions/bcadb20c-ac04-4561-8d19-6c8c129312c9

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_toReal_budget_to_ennreal_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) (B : ℝ)
    (Term : Ω → ℝ) (hTermI : Integrable Term P)
    (hTermNonneg : ∀ ω, 0 ≤ Term ω)
    (hBudget :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
        (∫ ω, Term ω ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal B := by
  have hTermMean : 0 ≤ ∫ ω, Term ω ∂P :=
    integral_nonneg hTermNonneg
  have hCashBudget :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) ≤ B := by
    linarith
  have hBound :=
    avram_wave7_03_original_bounded_random_clock_toReal_budget_to_ennreal_cash
      X x C D hD q hq ⟨T, hT⟩ (fun _ : Ω => ⟨T, hT⟩)
      (by intro ω; exact le_refl _)
      (by exact measurable_const)
      B hCashBudget
  exact hBound
