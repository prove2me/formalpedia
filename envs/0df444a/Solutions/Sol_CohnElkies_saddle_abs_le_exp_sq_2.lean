-- Prove2me | solution 2 for CohnElkies.saddle_abs_le_exp_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/40130c1e-58e5-49db-9395-0a0bfb7a310e

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CohnElkies
theorem _root_.solution (T : ℝ) :
    |T| ≤ Real.exp (T ^ 2) := by
  have hsquare : (|T| - 1) ^ 2 ≥ 0 := sq_nonneg _
  have habs : |T| ^ 2 = T ^ 2 := sq_abs T
  have hlinear : |T| ≤ 1 + T ^ 2 := by
    nlinarith [abs_nonneg T, sq_nonneg T]
  exact hlinear.trans (by
    simpa [add_comm] using! Real.add_one_le_exp (T ^ 2))
end CohnElkies
