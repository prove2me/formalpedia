-- Prove2me | solution 1 for CohnElkies.saddleSource_central_rpow_div_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/b66b1c0b-4a27-4ac2-8838-bb56e5b50a5b

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
    {x : ℝ} (hx : 0 < x) :
    x ^ (1 / 12 : ℝ) / Real.sqrt x =
      x ^ (-(5 / 12 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hx]
  norm_num
end CohnElkies
