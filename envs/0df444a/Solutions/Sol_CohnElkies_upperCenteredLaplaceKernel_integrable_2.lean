-- Prove2me | solution 2 for CohnElkies.upperCenteredLaplaceKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:41:13.478047+00:00
-- url     : https://prove2.me/submissions/5aaeb9bd-431d-44f7-995b-7c518cdf1537

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    {c : ℝ} (hc : 0 < c) (T : ℝ) :
    IntegrableOn (upperCenteredLaplaceKernel c T)
      (Ioi 0) := by
  have hg : IntegrableOn (fun a : ℝ => 2 * |T| * Real.exp (-c * a)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hc).const_mul _
  refine hg.mono' ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro a ha
    have ha' : a ≠ 0 := (ne_of_gt ha)
    unfold upperCenteredLaplaceKernel upperImaginaryExp
    apply ContinuousAt.continuousWithinAt
    have : ContinuousAt (fun a : ℝ => Real.exp (-c * a) / a) a :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt.div continuousAt_id ha'
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
    intro a ha
    have ha0 : (0:ℝ) < a := ha
    unfold upperCenteredLaplaceKernel upperImaginaryExp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h1 : ‖Complex.exp (Complex.I * ((a * T : ℝ) : ℂ)) - 1 - Complex.I * ((a * T : ℝ) : ℂ)‖ ≤ 2 * (a * |T|) := by
      have e1 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a * T)
      calc _ ≤ ‖Complex.exp (Complex.I * ((a * T : ℝ) : ℂ)) - 1‖ + ‖Complex.I * ((a * T : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ ≤ ‖a * T‖ + ‖a * T‖ := by
            gcongr
            rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
        _ = 2 * (a * |T|) := by rw [Real.norm_eq_abs, abs_mul, abs_of_pos ha0]; ring
    have hcast : ((a * T : ℝ) : ℂ) = (a : ℂ) * (T : ℂ) := by push_cast; ring
    calc _ ≤ 2 * (a * |T|) * (Real.exp (-c * a) / a) := by gcongr
      _ = 2 * |T| * Real.exp (-c * a) := by field_simp

