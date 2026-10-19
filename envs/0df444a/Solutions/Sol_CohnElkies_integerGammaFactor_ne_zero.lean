-- Prove2me | solution 1 for CohnElkies.integerGammaFactor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/32300761-7d44-45fc-86c0-48351e8d112d

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
    (j : ℕ) {y : ℝ} (hy : y ≠ 0) :
    (j : ℂ) + Complex.I * (y : ℂ) / 2 ≠ 0 := by
  intro hz
  have him := congrArg Complex.im hz
  norm_num at him
  exact hy (by linarith)
end CohnElkies
