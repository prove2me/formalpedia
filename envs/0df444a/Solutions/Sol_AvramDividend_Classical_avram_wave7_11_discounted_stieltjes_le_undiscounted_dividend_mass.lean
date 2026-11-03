-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_discounted_stieltjes_le_undiscounted_dividend_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:46:17.129196+00:00
-- url     : https://prove2.me/submissions/587da932-4a06-4aa0-8222-571e90260464

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

/-- Pointwise original Stieltjes discounted reward is bounded by the full
    dividend mass of the identical measurable real-time payment set. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (σ : ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      (dividendMeasure D ω) (paymentTimes σ ∩ Iic T) := by
  have hs : MeasurableSet (paymentTimes σ ∩ Iic T) :=
    (paymentTimes_measurable σ).inter measurableSet_Iic
  calc
    _ ≤ (∫⁻ t in paymentTimes σ ∩ Iic T,
        (1 : ℝ≥0∞) ∂(dividendMeasure D ω)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hs] with t ht
      have hqt : 0 ≤ q * t := mul_nonneg hq ht.1.1
      have hexp : Real.exp (-(q * t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqt)
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hexp
    _ = (dividendMeasure D ω) (paymentTimes σ ∩ Iic T) := by simp
