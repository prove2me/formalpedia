-- Prove2me | solution 1 for CohnElkies.upper_one_sub_cos_le_min
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:18:14.867428+00:00
-- url     : https://prove2.me/submissions/1eacf105-fb35-42bd-b19d-64d1f62ffaa7

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution (x : ℝ) :
    1 - Real.cos x ≤ min (x ^ 2 / 2) 2 := by
  refine le_min ?_ ?_
  · have := Real.one_sub_sq_div_two_le_cos (x := x); linarith
  · linarith [Real.neg_one_le_cos x]

