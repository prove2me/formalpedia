-- Prove2me | solution 2 for CohnElkies.upper_one_sub_cos_le_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/ab931a08-c343-4757-927c-082f08bfb76b

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
theorem _root_.solution (x : ℝ) :
    1 - Real.cos x ≤ min (x ^ 2 / 2) 2 := by
  apply le_min
  · nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  · nlinarith [Real.neg_one_le_cos x]
end CohnElkies
