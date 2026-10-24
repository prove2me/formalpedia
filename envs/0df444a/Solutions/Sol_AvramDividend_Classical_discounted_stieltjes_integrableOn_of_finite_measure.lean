-- Prove2me | solution 1 for AvramDividend.Classical.discounted_stieltjes_integrableOn_of_finite_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:57:58.934982+00:00
-- url     : https://prove2.me/submissions/e2b65320-0b95-4a1f-8475-92be7ab85d78

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Discounted payout rates are integrable on nonnegative payment times
    whenever the corresponding Stieltjes measure has finite mass there. -/
theorem solution
    (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (A : Set ℝ)
    (hAmeas : MeasurableSet A)
    (hAnonneg : ∀ t ∈ A, 0 ≤ t)
    (hfinite : μ A ≠ ⊤) :
    IntegrableOn (fun t : ℝ => Real.exp (-(q * t))) A μ := by
  refine Measure.integrableOn_of_bounded (M := 1) hfinite ?_ ?_
  · have hcont : Continuous (fun t : ℝ => Real.exp (-(q * t))) := by fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem hAmeas] with t ht
    have hqt : 0 ≤ q * t := mul_nonneg hq (hAnonneg t ht)
    have hbound : Real.exp (-(q * t)) ≤ 1 := by
      calc
        Real.exp (-(q * t)) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (neg_nonpos.mpr hqt)
        _ = 1 := Real.exp_zero
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hbound
