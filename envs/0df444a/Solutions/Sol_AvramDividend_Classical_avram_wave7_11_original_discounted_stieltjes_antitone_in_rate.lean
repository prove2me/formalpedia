-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_original_discounted_stieltjes_antitone_in_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:46:20.898681+00:00
-- url     : https://prove2.me/submissions/e5909343-660b-463e-89b5-c9d0207a5e41

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The full original-path Stieltjes reward is antitone in the discount
    rate on the identical measurable nonnegative payment-time set. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (σ : ℝ≥0∞)
    (T q₁ q₂ : ℝ) (hq : q₁ ≤ q₂) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q₂ * t))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q₁ * t))) ∂(dividendMeasure D ω)) := by
  have hs : MeasurableSet (paymentTimes σ ∩ Iic T) :=
    (paymentTimes_measurable σ).inter measurableSet_Iic
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hs] with t ht
  have hmul : q₁ * t ≤ q₂ * t :=
    mul_le_mul_of_nonneg_right hq ht.1.1
  have hreal : Real.exp (-(q₂ * t)) ≤ Real.exp (-(q₁ * t)) :=
    Real.exp_le_exp.mpr (neg_le_neg hmul)
  exact ENNReal.ofReal_le_ofReal hreal
