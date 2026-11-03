-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_real_bounded_random_clock_signed_stieltjes_budget_to_ennreal_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:40:55.891865+00:00
-- url     : https://prove2.me/submissions/813ec76f-5f2e-4f09-b4ed-876dc23894a6

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_bounded_real_random_clock_full_stieltjes_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- A true signed real Stieltjes budget on the original real bounded
    random clock controls the exact stopped double-ENNReal dividends. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ) (hT : 0 ≤ T) (τ : Ω → ℝ)
    (hτNonneg : ∀ ω, 0 ≤ τ ω)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable τ) (B : ℝ)
    (hBudget :
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by
  rw [avram_wave7_03_original_real_bounded_real_random_clock_full_stieltjes_mean_eq
    X x C D hD q hq T hT τ hτNonneg hτBound hτMeas]
  exact ENNReal.ofReal_le_ofReal hBudget
