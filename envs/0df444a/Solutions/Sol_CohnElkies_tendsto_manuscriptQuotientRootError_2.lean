-- Prove2me | solution 2 for CohnElkies.tendsto_manuscriptQuotientRootError
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:33:32.060763+00:00
-- url     : https://prove2.me/submissions/fd525c59-7282-4738-b61a-6aaa91dd6fb6

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_sharpAsymptotics
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology


theorem solution :
    Tendsto manuscriptQuotientRootError atTop (nhds (0 : ℝ)) := by
  have h : Tendsto normalizedProgram atTop (nhds criticalRadius) := CohnElkies.sharpAsymptotics.1
  have := h.sub_const criticalRadius
  rw [sub_self] at this
  exact this

