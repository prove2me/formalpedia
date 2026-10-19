-- Prove2me | solution 1 for CohnElkies.saddle_sqrt_le_one_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/7f778f91-e014-4aa2-ab13-bc59c5d92409

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x ≤ 1 + x := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · linarith
  · nlinarith [sq_nonneg x]
end CohnElkies
