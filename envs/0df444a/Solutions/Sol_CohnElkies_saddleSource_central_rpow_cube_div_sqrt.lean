-- Prove2me | solution 1 for CohnElkies.saddleSource_central_rpow_cube_div_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/d0f1e05c-fd54-4fb8-ab2a-0176832947eb

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
    (x ^ (1 / 12 : ℝ)) ^ 3 / Real.sqrt x =
      x ^ (-(1 / 4 : ℝ)) := by
  have hcube :
      (x ^ (1 / 12 : ℝ)) ^ 3 =
        x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  rw [hcube, Real.sqrt_eq_rpow,
    ← Real.rpow_sub hx]
  norm_num
end CohnElkies
