-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_uniform_signed_budgets_valueFunction_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:03:58.771171+00:00
-- url     : https://prove2.me/submissions/ce942c0d-5046-46d6-9d17-7bde0c899186

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

/-- For all original admissible strategies, uniform true signed Stieltjes
    horizon bounds control the canonical unrestricted dividend value supremum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (q : ℝ) (hq : 0 ≤ q) (B : ℝ)
    (hBudget : ∀ (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
      (n : ℕ),
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    valueFunction X q x ≤ ENNReal.ofReal B := by
  unfold valueFunction
  refine iSup_le fun D => iSup_le fun hD => ?_
  have hDtop : IsAdmissibleLe X x ⊤ D := by
    refine ⟨hD, ?_⟩
    intro ω t ht
    exact le_top
  change (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
    ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B
  exact avram_wave7_03_original_uniform_signed_horizon_budgets_imply_perpetual_ennreal
    X x ⊤ D hDtop q hq B (hBudget D hD)
