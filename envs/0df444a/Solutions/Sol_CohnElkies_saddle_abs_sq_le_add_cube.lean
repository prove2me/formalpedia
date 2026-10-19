-- Prove2me | solution 1 for CohnElkies.saddle_abs_sq_le_add_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/785c8e33-8c3d-4ff7-a71b-6c42a05604d2

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
    |T| ^ 2 ≤ |T| + |T| ^ 3 := by
  have hfactor :
      0 ≤ |T| * (|T| - (1 / 2 : ℝ)) ^ 2 :=
    mul_nonneg (abs_nonneg T) (sq_nonneg _)
  nlinarith [abs_nonneg T]
end CohnElkies
