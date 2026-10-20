-- Prove2me | solution 2 for CohnElkies.lowerCoth_log_small_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:53:43.841692+00:00
-- url     : https://prove2.me/submissions/26d94a09-e0e3-4bc9-8211-a49ebf513415

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology


theorem solution
    {y : ℝ} (hy : y ≠ 0) (hsmall : |y| ≤ 1) :
    Real.log (lowerCoth (Real.pi * |y| / 2)) ≤
      Real.pi + |Real.log Real.pi| +
        3 * (|Real.log (|y|)| + |Real.log (2 : ℝ)|) := by
  have hpi := Real.pi_pos
  have hy0 : 0 < |y| := abs_pos.mpr hy
  have hx : 0 < Real.pi * |y| / 2 := by positivity
  set x := Real.pi * |y| / 2 with hxdef
  have hxle : x ≤ Real.pi / 2 := by rw [hxdef]; nlinarith
  have hsinh : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx.le
  have hsp : 0 < Real.sinh x := lt_of_lt_of_le hx hsinh
  have hcosh : Real.cosh x ≤ Real.exp x := by
    rw [Real.cosh_eq]; linarith [Real.exp_le_exp.mpr (show -x ≤ x by linarith)]
  have hcoth : lowerCoth x ≤ Real.exp x / x := by
    unfold lowerCoth
    rw [div_le_div_iff₀ hsp hx]
    nlinarith [Real.cosh_pos x, Real.exp_pos x]
  have hcpos : 0 < lowerCoth x := by
    unfold lowerCoth; exact div_pos (Real.cosh_pos x) hsp
  have h1 : Real.log (lowerCoth x) ≤ x - Real.log x := by
    calc Real.log (lowerCoth x) ≤ Real.log (Real.exp x / x) := Real.log_le_log hcpos hcoth
      _ = x - Real.log x := by rw [Real.log_div (Real.exp_pos x).ne' hx.ne', Real.log_exp]
  have h2 : Real.log x = Real.log Real.pi + Real.log |y| - Real.log 2 := by
    rw [hxdef, Real.log_div (by positivity) (by norm_num), Real.log_mul hpi.ne' hy0.ne']
  have h3 : -Real.log Real.pi ≤ |Real.log Real.pi| := neg_le_abs _
  have h4 : -Real.log |y| ≤ |Real.log (|y|)| := neg_le_abs _
  have h5 : 0 ≤ |Real.log (|y|)| := abs_nonneg _
  have h6 : Real.log 2 ≤ |Real.log 2| := le_abs_self _
  have h7 : 0 ≤ |Real.log 2| := abs_nonneg _
  linarith

