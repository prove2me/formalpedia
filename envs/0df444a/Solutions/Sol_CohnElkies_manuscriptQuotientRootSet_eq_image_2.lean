-- Prove2me | solution 2 for CohnElkies.manuscriptQuotientRootSet_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:33:16.050313+00:00
-- url     : https://prove2.me/submissions/1d2a993a-c4d8-4017-b57b-5debef0486f8

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology


theorem solution (d : ℕ) :
    manuscriptQuotientRootSet d =
      (fun x : ℝ => x ^ ((d : ℝ)⁻¹)) '' quotientSet d := by
  unfold manuscriptQuotientRootSet quotientSet
  rw [← Set.range_comp]
  rfl

