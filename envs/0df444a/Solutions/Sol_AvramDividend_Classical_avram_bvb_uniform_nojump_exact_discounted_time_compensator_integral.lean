-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_uniform_nojump_exact_discounted_time_compensator_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:17:48.616898+00:00
-- url     : https://prove2.me/submissions/a7e34be7-b215-4a49-b814-440bcc170549

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory intervalIntegral Real
theorem solution (T : ℝ) :
    (∫ t in (0 : ℝ)..T, Real.exp (-t)) =
      1 - Real.exp (-T) := by
  calc
    (∫ t in (0 : ℝ)..T, Real.exp (-t)) =
        ∫ x in (-T)..0, Real.exp x := by
      simpa using
        (intervalIntegral.integral_comp_neg
          (f := Real.exp) (a := (0 : ℝ)) (b := T))
    _ = 1 - Real.exp (-T) := by
      rw [integral_exp]
      simp
