-- Prove2me | solution 2 for CohnElkies.sharpQuotient_of_eventual_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:18:30.961948+00:00
-- url     : https://prove2.me/submissions/ae5d0f96-a45b-469e-b51b-5f6ca58b7390

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


theorem solution
    (hlower : EventualLowerBound)
    (hupper : EventualUpperBound) :
    SharpQuotientAsymptotic := by
  unfold SharpQuotientAsymptotic
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [hlower ((a + criticalRadius) / 2) (by linarith)] with d hd
    linarith
  · filter_upwards [hupper ((a + criticalRadius) / 2) (by linarith)] with d hd
    linarith

