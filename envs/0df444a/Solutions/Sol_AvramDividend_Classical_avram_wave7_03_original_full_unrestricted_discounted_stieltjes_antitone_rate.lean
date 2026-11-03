-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_full_unrestricted_discounted_stieltjes_antitone_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:01:33.371134+00:00
-- url     : https://prove2.me/submissions/59ebad62-d08d-46c4-a4a0-5d9784772d4a

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

/-- Full source Stieltjes cash, including the time-zero atom and every genuine
    pre-ruin payment, decreases as the discount rate increases. -/
/- Recovered complete original Stieltjes proof after terminal remote storage failure. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (σ : ℝ≥0∞)
    (q₁ q₂ : ℝ) (hq : q₁ ≤ q₂) :
    (∫⁻ t in paymentTimes σ,
      ENNReal.ofReal (Real.exp (-(q₂ * t))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ t in paymentTimes σ,
      ENNReal.ofReal (Real.exp (-(q₁ * t))) ∂(dividendMeasure D ω)) := by
  have hs : MeasurableSet (paymentTimes σ) := paymentTimes_measurable σ
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hs] with t ht
  have hmul : q₁ * t ≤ q₂ * t :=
    mul_le_mul_of_nonneg_right hq ht.1
  have hreal : Real.exp (-(q₂ * t)) ≤ Real.exp (-(q₁ * t)) :=
    Real.exp_le_exp.mpr (neg_le_neg hmul)
  exact ENNReal.ofReal_le_ofReal hreal
