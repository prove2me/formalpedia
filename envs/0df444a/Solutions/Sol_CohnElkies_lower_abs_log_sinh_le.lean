-- Prove2me | solution 1 for CohnElkies.lower_abs_log_sinh_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/fe5092a9-4a4e-4283-b823-3b5b2cd03075

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lower_sinh_le_exp

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
    |Real.log (Real.sinh x)| ≤ x + |Real.log x| := by
  have hlower : x ≤ Real.sinh x :=
    Real.self_le_sinh_iff.mpr hx.le
  have hsinh : 0 < Real.sinh x := hx.trans_le hlower
  by_cases hlarge : 1 ≤ Real.sinh x
  · rw [abs_of_nonneg (Real.log_nonneg hlarge)]
    have hlog := Real.log_le_log hsinh
      (lower_sinh_le_exp x)
    have habs := abs_nonneg (Real.log x)
    rw [Real.log_exp] at hlog
    linarith
  · rw [abs_of_nonpos
      (Real.log_nonpos hsinh.le (le_of_not_ge hlarge))]
    have hlog := Real.log_le_log hx hlower
    have habs := neg_le_abs (Real.log x)
    linarith
end CohnElkies
