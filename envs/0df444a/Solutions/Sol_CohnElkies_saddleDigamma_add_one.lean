-- Prove2me | solution 1 for CohnElkies.saddleDigamma_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/e7266653-b435-456f-b404-1403da01178c

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {m : ℝ} (hm : 0 < m) :
    saddleDigamma (m + 1) =
      saddleDigamma m + m⁻¹ := by
  unfold saddleDigamma
  rw [← deriv_comp_add_const,
    ← Real.deriv_log,
    ← deriv_add
      (saddleLogGamma_differentiableAt hm)
      (Real.differentiableAt_log hm.ne')]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds hm]
    with x hx
  exact saddleLogGamma_add_one hx
end CohnElkies
