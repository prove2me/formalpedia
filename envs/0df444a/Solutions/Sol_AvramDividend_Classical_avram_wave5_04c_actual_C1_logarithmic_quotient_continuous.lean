-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_C1_logarithmic_quotient_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:30:22.211862+00:00
-- url     : https://prove2.me/submissions/e9e813b5-93f6-4e34-b1af-641b17abe486

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_extended_difference_quotient_continuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set Filter
open AvramDividend.Classical

/-! The exact C1 payoff logarithmic chord quotient extends continuously
to a compact interval [a,1] avoiding the logarithmic singularity. -/
theorem solution (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (x a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ContinuousOn
      (Function.update
        (fun t : ℝ =>
          (w (x + Real.log t) - w x) / (t - 1))
        1 (deriv w x)) (Icc a 1) := by
  let g : ℝ → ℝ := fun t => w (x + Real.log t)
  have hdw : Differentiable ℝ w :=
    hw.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hw' : HasDerivAt w (deriv w x) x :=
    hdw.differentiableAt.hasDerivAt
  have hlog : HasDerivAt Real.log 1 1 := by
    convert Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0) using 1 <;> norm_num
  have hsum : HasDerivAt (fun t : ℝ => x + Real.log t) 1 1 := by
    convert hlog.const_add x using 1 <;> norm_num
  have hg : HasDerivAt g (deriv w x) 1 := by
    have hw1 : HasDerivAt w (deriv w x) (x + Real.log 1) := by
      simpa using hw'
    convert hw1.comp 1 hsum using 1 <;>
      first | rfl | ring | simp [g, Function.comp_def]
  have hfc : ∀ t ∈ Icc a 1, t ≠ 1 → ContinuousAt g t := by
    intro t ht hne
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    have hlogcont : ContinuousAt Real.log t :=
      (Real.hasDerivAt_log (ne_of_gt htpos)).continuousAt
    let inner : ℝ → ℝ := fun s => x + Real.log s
    have hinner : ContinuousAt inner t :=
      continuousAt_const.add hlogcont
    have hwcont : ContinuousAt w (inner t) :=
      hdw.continuous.continuousAt
    have hcomp : ContinuousAt (w ∘ inner) t :=
      hwcont.comp hinner
    simpa only [Function.comp_def, inner, g] using hcomp
  have h := avram_wave5_04c_C1_extended_difference_quotient_continuous
    g 1 (deriv w x) hg (Icc a 1) hfc
  simpa only [g, Real.log_one, add_zero] using h
