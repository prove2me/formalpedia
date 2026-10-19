-- Prove2me | solution 1 for CohnElkies.lowerCoth_log_small_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/a36c0e02-b573-4cf1-8b7a-db63e219a10a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerCoth_pos
import Theorems.Thm_CohnElkies_lower_abs_log_coth_div_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {y : ℝ} (hy : y ≠ 0) (hsmall : |y| ≤ 1) :
    Real.log (lowerCoth (Real.pi * |y| / 2)) ≤
      Real.pi + |Real.log Real.pi| +
        3 * (|Real.log (|y|)| + |Real.log (2 : ℝ)|) := by
  have hu : 0 < |y| / 2 := by positivity
  have hpiu : 0 < Real.pi * (|y| / 2) :=
    mul_pos Real.pi_pos hu
  have hcoth : 0 < lowerCoth (Real.pi * (|y| / 2)) :=
    lowerCoth_pos hpiu
  have hloghalf :
      |Real.log (|y| / 2)| ≤
        |Real.log (|y|)| + |Real.log (2 : ℝ)| := by
    rw [Real.log_div (abs_ne_zero.mpr hy) (by norm_num)]
    exact abs_sub _ _
  have hbase := lower_abs_log_coth_div_le hu
  have hdecomp :
      Real.log (lowerCoth (Real.pi * (|y| / 2))) =
        Real.log
          (lowerCoth (Real.pi * (|y| / 2)) / (|y| / 2)) +
            Real.log (|y| / 2) := by
    rw [Real.log_div hcoth.ne' hu.ne']
    ring
  rw [show Real.pi * |y| / 2 =
    Real.pi * (|y| / 2) by ring]
  rw [hdecomp]
  have hlogdiv := le_abs_self
    (Real.log (lowerCoth (Real.pi * (|y| / 2)) / (|y| / 2)))
  have hlogu := le_abs_self (Real.log (|y| / 2))
  have hpibound : 2 * (Real.pi * (|y| / 2)) ≤ Real.pi := by
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hsmall)]
  linarith
end CohnElkies
