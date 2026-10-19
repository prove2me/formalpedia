-- Prove2me | solution 2 for CohnElkies.saddle_abs_sq_le_add_cube
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:19:57.661975+00:00
-- url     : https://prove2.me/submissions/ac4c36a7-7ab3-46cb-a43b-9c9a90dc5dc0

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
    |T| ^ 2 ≤ |T| + |T| ^ 3 := by
  have ha := abs_nonneg T
  nlinarith [mul_nonneg ha (sq_nonneg (|T| - 1/2)), pow_two_nonneg (|T|)]

