-- Prove2me | solution 2 for CohnElkies.tendsto_saddleDigamma_atTop
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:00.529466+00:00
-- url     : https://prove2.me/submissions/cf817795-75d7-4943-933e-b30b784fe240

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


theorem solution :
    Tendsto saddleDigamma atTop atTop := by
  have h := tendsto_saddleDigamma_sub_log.add_atTop Real.tendsto_log_atTop
  refine h.congr ?_
  intro x; simp

