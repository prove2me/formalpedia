-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_uniform_signed_budgets_perpetual_cash_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:50:11.135191+00:00
-- url     : https://prove2.me/submissions/9b857c84-bc52-408b-bffd-fb8a8c765fe0

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

/-- Uniform genuine original signed Stieltjes budgets force finite
    perpetual ENNReal cash at the exact untruncated original payment set. -/
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
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≠ ⊤ := by
  have hCash :=
    avram_wave7_03_original_uniform_signed_horizon_budgets_imply_perpetual_ennreal
      X x C D hD q hq B hBudget
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hCash
