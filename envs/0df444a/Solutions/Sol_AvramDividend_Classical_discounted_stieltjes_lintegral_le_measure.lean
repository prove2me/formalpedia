-- Prove2me | solution 1 for AvramDividend.Classical.discounted_stieltjes_lintegral_le_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:01:40.684671+00:00
-- url     : https://prove2.me/submissions/4b38fbc7-1e1b-46e1-a474-c615375209da

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- A nonnegative-rate discounted Stieltjes payout on any nonnegative time
    region is bounded by the undiscounted measure of that region. -/
theorem solution
    (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (A : Set ℝ)
    (hAmeas : MeasurableSet A)
    (hAnonneg : ∀ t ∈ A, 0 ≤ t) :
    (∫⁻ t in A, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤ μ A := by
  calc
    (∫⁻ t in A, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤
        (∫⁻ t in A, (1 : ℝ≥0∞) ∂μ) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem hAmeas] with t ht
      have hqt : 0 ≤ q * t := mul_nonneg hq (hAnonneg t ht)
      apply ENNReal.ofReal_le_one.mpr
      calc
        Real.exp (-(q * t)) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (neg_nonpos.mpr hqt)
        _ = 1 := Real.exp_zero
    _ = μ A := by
      rw [MeasureTheory.lintegral_one]
      simp
