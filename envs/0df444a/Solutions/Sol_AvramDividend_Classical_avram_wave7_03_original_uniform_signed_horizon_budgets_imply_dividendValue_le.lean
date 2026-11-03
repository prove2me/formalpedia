-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:02:35.209935+00:00
-- url     : https://prove2.me/submissions/e72f01e9-b6ae-48d7-b164-6707503a9dde

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_perpetual_ennreal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- An original real signed Stieltjes budget on all finite horizons
    controls the canonical full dividendValue, including its atom at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (B : ℝ)
    (hBudget : ∀ n : ℕ,
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    dividendValue X q x D ≤ ENNReal.ofReal B := by
  change (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
    ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B
  exact avram_wave7_03_original_uniform_signed_horizon_budgets_imply_perpetual_ennreal
    X x C D hD q hq B hBudget
