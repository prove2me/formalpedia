-- Prove2me | solution 1 for CohnElkies.sharpQuotient_of_eventual_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/6036099d-8b41-4405-bac2-9e7126717c3c

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
namespace CohnElkies
theorem _root_.solution
    (hlower : EventualLowerBound)
    (hupper : EventualUpperBound) :
    SharpQuotientAsymptotic := by
  unfold SharpQuotientAsymptotic
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have hmid : (a + criticalRadius) / 2 < criticalRadius := by
      linarith
    filter_upwards [hlower _ hmid] with d hd
    linarith
  · intro b hb
    have hmid : criticalRadius < (criticalRadius + b) / 2 := by
      linarith
    filter_upwards [hupper _ hmid] with d hd
    linarith
end CohnElkies
