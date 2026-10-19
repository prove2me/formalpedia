-- Prove2me | solution 2 for CohnElkies.lowerEndpointPhase_continuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:50:57.256607+00:00
-- url     : https://prove2.me/submissions/05919f80-2789-4787-8241-456438ebe2c1

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology


theorem solution :
    Continuous lowerEndpointPhase := by
  unfold lowerEndpointPhase
  have h : ∀ T : ℝ, 0 < 1 + T ^ 2 / 4 := fun T => by positivity
  fun_prop (disch := exact fun T => (h T).ne')

