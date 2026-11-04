-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_true_stopped_cash_antitone_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:27:27.432123+00:00
-- url     : https://prove2.me/submissions/57ee2184-445c-4e4e-b803-fc568168146c

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Larger nonnegative discount rates lower the original stopped dividend Cash lintegral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (T : ℝ≥0)
    (q₁ q₂ : ℝ) (hq : q₁ ≤ q₂) :
    (∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q₂ * s))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q₁ * s))) ∂(dividendMeasure D ω)) := by
  have hs : MeasurableSet (paymentTimes σ ∩ Iic (T : ℝ)) :=
    (paymentTimes_measurable σ).inter measurableSet_Iic
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hs] with s hs
  have hs0 : 0 ≤ s :=
    (paymentTimes_membership_to_nNReal_active σ s hs.1).1
  have hprod : q₁ * s ≤ q₂ * s :=
    mul_le_mul_of_nonneg_right hq hs0
  exact ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr (neg_le_neg hprod))
