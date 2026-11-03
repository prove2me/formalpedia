-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_uniform_signed_budgets_perpetual_toReal_cash_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:55:16.350067+00:00
-- url     : https://prove2.me/submissions/21ec6a29-cb0f-41da-9207-f436e9944253

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

/-- A uniform true source real signed horizon budget controls the toReal
    of complete ruin-stopped perpetual ENNReal dividends. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (B : ℝ) (hB : 0 ≤ B)
    (hBudget : ∀ n : ℕ,
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P).toReal ≤ B := by
  have hCash :=
    avram_wave7_03_original_uniform_signed_horizon_budgets_imply_perpetual_ennreal
      X x C D hD q hq B hBudget
  have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hCash
  simpa only [ENNReal.toReal_ofReal hB] using hReal
