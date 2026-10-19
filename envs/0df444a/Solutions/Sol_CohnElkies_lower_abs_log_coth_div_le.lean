-- Prove2me | solution 1 for CohnElkies.lower_abs_log_coth_div_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/74253531-f423-43c8-a38f-85087d64a09a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lower_abs_log_cosh_le
import Theorems.Thm_CohnElkies_lower_abs_log_sinh_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution {x : ℝ} (hx : 0 < x) :
    |Real.log (lowerCoth (Real.pi * x) / x)| ≤
      2 * (Real.pi * x) +
        |Real.log Real.pi| + 2 * |Real.log x| := by
  have ht : 0 < Real.pi * x := mul_pos Real.pi_pos hx
  have hsinh : Real.sinh (Real.pi * x) ≠ 0 :=
    Real.sinh_ne_zero.mpr ht.ne'
  have hcosh : Real.cosh (Real.pi * x) ≠ 0 :=
    (Real.cosh_pos _).ne'
  have hlogpi :
      |Real.log (Real.pi * x)| ≤
        |Real.log Real.pi| + |Real.log x| := by
    rw [Real.log_mul Real.pi_ne_zero hx.ne']
    simpa [sub_neg_eq_add] using!
      (abs_sub (Real.log Real.pi) (-(Real.log x)))
  have hcoshbound := lower_abs_log_cosh_le ht.le
  have hsinhbound := lower_abs_log_sinh_le ht
  unfold lowerCoth
  rw [Real.log_div (div_ne_zero hcosh hsinh) hx.ne',
    Real.log_div hcosh hsinh]
  calc
    |(Real.log (Real.cosh (Real.pi * x)) -
        Real.log (Real.sinh (Real.pi * x))) - Real.log x| ≤
      (|Real.log (Real.cosh (Real.pi * x))| +
        |Real.log (Real.sinh (Real.pi * x))|) +
          |Real.log x| := by
      have hfirst :=
        abs_sub
          (Real.log (Real.cosh (Real.pi * x)))
          (Real.log (Real.sinh (Real.pi * x)))
      have hsecond :=
        abs_sub
          (Real.log (Real.cosh (Real.pi * x)) -
            Real.log (Real.sinh (Real.pi * x)))
          (Real.log x)
      linarith
    _ ≤ 2 * (Real.pi * x) +
        |Real.log Real.pi| + 2 * |Real.log x| := by
      linarith
end CohnElkies
