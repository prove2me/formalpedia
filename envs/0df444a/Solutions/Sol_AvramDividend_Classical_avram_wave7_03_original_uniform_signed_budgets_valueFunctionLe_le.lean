-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_uniform_signed_budgets_valueFunctionLe_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:03:28.752086+00:00
-- url     : https://prove2.me/submissions/4889ad35-83c4-4f79-bcf0-9a0f9a4f2332

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

/-- Original capped value-function bound from true signed Stieltjes
    expectations, uniform in both the admissible strategy and time horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (B : ℝ)
    (hBudget : ∀ (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
      (n : ℕ),
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    valueFunctionLe X q C x ≤ ENNReal.ofReal B := by
  unfold valueFunctionLe
  refine iSup_le fun D => iSup_le fun hD => ?_
  change (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
    ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B
  exact avram_wave7_03_original_uniform_signed_horizon_budgets_imply_perpetual_ennreal
    X x C D hD q hq B (hBudget D hD)
