-- Prove2me | solution 1 for CohnElkies.lowerRiemannLog_one_nonneg_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/81ee8300-23e1-4fbb-9535-e5d89bc38af8

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution (T : ℝ) :
    0 ≤ lowerRiemannLog T 1 ∧
      lowerRiemannLog T 1 ≤ |T| / 2 := by
  have hrad : 0 < (1 : ℝ) + T ^ 2 / 4 := by
    nlinarith [sq_nonneg T]
  have hsqrtone :
      1 ≤ Real.sqrt ((1 : ℝ) + T ^ 2 / 4) := by
    apply (Real.le_sqrt (by norm_num) hrad.le).2
    nlinarith [sq_nonneg T]
  have hsqrtupper :
      Real.sqrt ((1 : ℝ) + T ^ 2 / 4) ≤
        1 + |T| / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [abs_nonneg T, sq_abs T]
  unfold lowerRiemannLog
  simp only [one_pow]
  constructor
  · exact Real.log_nonneg hsqrtone
  · have hlog := Real.log_le_sub_one_of_pos
      (Real.sqrt_pos.mpr hrad)
    linarith
end CohnElkies
