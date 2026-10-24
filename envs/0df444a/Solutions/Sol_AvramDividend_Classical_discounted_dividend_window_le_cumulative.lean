-- Prove2me | solution 1 for AvramDividend.Classical.discounted_dividend_window_le_cumulative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:08:22.104293+00:00
-- url     : https://prove2.me/submissions/576d2431-2eba-42a3-a3de-df72f018a08d

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

/-- The actual discounted Stieltjes payout before any finite time is
    dominated by the finite cumulative dividend at the next time point. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0)
    (ω : Ω) :
    (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤ ENNReal.ofReal (D (T + 1) ω) := by
  have hTsucc : (T : ℝ) < ((T + 1 : ℝ≥0) : ℝ) := by
    exact_mod_cast
      (lt_add_of_pos_right T (by norm_num : (0 : ℝ≥0) < 1))
  have hsubset :
      paymentTimes σ ∩ Iic (T : ℝ) ⊆
        Ico (0 : ℝ) ((T + 1 : ℝ≥0) : ℝ) := by
    intro t ht
    exact ⟨ht.1.1, lt_of_le_of_lt ht.2 hTsucc⟩
  have hAmeas : MeasurableSet (paymentTimes σ ∩ Iic (T : ℝ)) :=
    (paymentTimes_measurable σ).inter measurableSet_Iic
  have hAnonneg : ∀ t ∈ paymentTimes σ ∩ Iic (T : ℝ), 0 ≤ t := by
    intro t ht
    exact ht.1.1
  have hDiscount :=
    discounted_stieltjes_lintegral_le_measure q hq
      (dividendMeasure D ω) (paymentTimes σ ∩ Iic (T : ℝ))
      hAmeas hAnonneg
  have hMass := measure_mono (μ := dividendMeasure D ω) hsubset
  rw [dividendMeasure_Ico_zero_eq_dividendValue D hD ω (T + 1)] at hMass
  exact hDiscount.trans hMass
