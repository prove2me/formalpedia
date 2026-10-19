-- Prove2me | solution 2 for CohnElkies.saddle_one_add_abs_cube_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/c34397e8-7fbe-44a7-ab48-e228583fc321

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
namespace CohnElkies
theorem _root_.solution (T : ℝ) :
    (1 + |T|) ^ 3 ≤ 4 * (1 + |T| ^ 3) := by
  have hfactor : 0 ≤
      (|T| - 1) ^ 2 * (|T| + 1) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith
end CohnElkies
