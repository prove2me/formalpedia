-- Prove2me | solution 1 for CohnElkies.lower_abs_log_sqrtFactor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/97555ec1-7615-48e2-b150-df39a1c1d845

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
namespace CohnElkies
theorem _root_.solution
    {c y : ℝ} (hc : 0 ≤ c) (hy : 0 < y) :
    |Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2))| ≤
      c + y / 2 + |Real.log (y / 2)| := by
  have ht : 0 < y / 2 := by positivity
  have hinside : 0 < c ^ 2 + (y / 2) ^ 2 := by
    nlinarith [sq_nonneg c, sq_pos_of_pos ht]
  have hsqrt : 0 < Real.sqrt (c ^ 2 + (y / 2) ^ 2) :=
    Real.sqrt_pos.2 hinside
  have hlower :
      y / 2 ≤ Real.sqrt (c ^ 2 + (y / 2) ^ 2) := by
    apply (Real.le_sqrt ht.le hinside.le).2
    nlinarith [sq_nonneg c]
  have hupper :
      Real.sqrt (c ^ 2 + (y / 2) ^ 2) ≤ c + y / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [mul_nonneg hc ht.le]
  by_cases hlarge : 1 ≤ Real.sqrt (c ^ 2 + (y / 2) ^ 2)
  · rw [abs_of_nonneg (Real.log_nonneg hlarge)]
    have hlog := Real.log_le_sub_one_of_pos hsqrt
    have habs := abs_nonneg (Real.log (y / 2))
    linarith
  · rw [abs_of_nonpos
      (Real.log_nonpos hsqrt.le (le_of_not_ge hlarge))]
    have hlog := Real.log_le_log ht hlower
    have habs := neg_le_abs (Real.log (y / 2))
    have hnonneg : 0 ≤ c + y / 2 := by positivity
    linarith
end CohnElkies
