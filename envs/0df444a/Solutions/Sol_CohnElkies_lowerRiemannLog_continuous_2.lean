-- Prove2me | solution 2 for CohnElkies.lowerRiemannLog_continuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:57:21.509918+00:00
-- url     : https://prove2.me/submissions/2303c201-6790-477b-a67f-e39e2583c25a

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


theorem solution
    {T : ℝ} (hT : T ≠ 0) :
    Continuous (lowerRiemannLog T) := by
  unfold lowerRiemannLog
  have hT2 : 0 < T^2 := lt_of_le_of_ne (sq_nonneg T) (Ne.symm (pow_ne_zero 2 hT))
  refine Continuous.log (Real.continuous_sqrt.comp (by fun_prop)) (fun x => ?_)
  exact (Real.sqrt_pos.2 (by nlinarith [sq_nonneg x])).ne'

