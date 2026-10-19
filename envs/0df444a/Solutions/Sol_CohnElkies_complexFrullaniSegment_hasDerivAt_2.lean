-- Prove2me | solution 2 for CohnElkies.complexFrullaniSegment_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:15:41.477113+00:00
-- url     : https://prove2.me/submissions/a24f5ff9-4d27-400f-9094-d7aab858ac0f

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


theorem solution
    (z w : ℂ) (s : ℝ) :
    HasDerivAt (complexFrullaniSegment z w) (w - z) s := by
  unfold complexFrullaniSegment
  have h : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
  have := (h.mul_const (w - z)).const_add z
  simpa using this

