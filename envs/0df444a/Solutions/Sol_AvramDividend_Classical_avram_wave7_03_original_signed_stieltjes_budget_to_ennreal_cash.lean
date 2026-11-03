-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_signed_stieltjes_budget_to_ennreal_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:12:04.088108+00:00
-- url     : https://prove2.me/submissions/58548661-038c-488a-b4ba-4f0c4419351f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_deterministic_horizon_mean_consumption
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- An actual real Stieltjes expected budget on the original stopped
    payment domain bounds precisely the original double-ENNReal cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (B : ℝ)
    (hBudget :
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by
  have hBridge :=
    avram_wave7_03_original_full_ruin_deterministic_horizon_mean_consumption
      X x C D hD q hq T.toNNReal
  have hTcast : (T.toNNReal : ℝ) = T := Real.coe_toNNReal T hT
  rw [hTcast] at hBridge
  rw [hBridge]
  exact ENNReal.ofReal_le_ofReal hBudget
