-- Prove2me | solution 1 for CohnElkies.saddle_one_add_abs_cube_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:18:14.84417+00:00
-- url     : https://prove2.me/submissions/906204fe-42e2-45c3-83f6-a62743beba15

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


theorem solution (T : ℝ) :
    (1 + |T|) ^ 3 ≤ 4 * (1 + |T| ^ 3) := by
  have h := abs_nonneg T
  nlinarith [sq_nonneg (|T| - 1), mul_nonneg h (sq_nonneg (|T| - 1)), sq_nonneg (|T|+1)]

