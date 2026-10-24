-- Prove2me | solution 1 for AvramDividend.Classical.expected_discounted_dividend_window_le_cumulative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:08:52.921123+00:00
-- url     : https://prove2.me/submissions/85bb35ac-35bb-4d03-bd9b-739346fe4ced

import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_lintegral_le_measure
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Expected stopped dividend reward is dominated by the expected total
    dividends paid by the subsequent time, with extended-real values. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞) (T : ℝ≥0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ∫⁻ ω, ENNReal.ofReal (D (T + 1) ω) ∂P := by
  apply lintegral_mono
  intro ω
  let σ₀ : ℝ≥0∞ := σ ω
  have hTsucc : (T : ℝ) < ((T + 1 : ℝ≥0) : ℝ) := by
    exact_mod_cast
      (lt_add_of_pos_right T (by norm_num : (0 : ℝ≥0) < 1))
  have hsubset :
      paymentTimes σ₀ ∩ Iic (T : ℝ) ⊆
        Ico (0 : ℝ) ((T + 1 : ℝ≥0) : ℝ) := by
    intro t ht
    exact ⟨ht.1.1, lt_of_le_of_lt ht.2 hTsucc⟩
  have hAmeas : MeasurableSet (paymentTimes σ₀ ∩ Iic (T : ℝ)) :=
    (paymentTimes_measurable σ₀).inter measurableSet_Iic
  have hAnonneg : ∀ t ∈ paymentTimes σ₀ ∩ Iic (T : ℝ), 0 ≤ t := by
    intro t ht
    exact ht.1.1
  have hDiscount :=
    discounted_stieltjes_lintegral_le_measure q hq
      (dividendMeasure D ω) (paymentTimes σ₀ ∩ Iic (T : ℝ))
      hAmeas hAnonneg
  have hMass := measure_mono (μ := dividendMeasure D ω) hsubset
  rw [dividendMeasure_Ico_zero_eq_dividendValue D hD ω (T + 1)] at hMass
  exact hDiscount.trans hMass
