-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_state2_requirements
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:38:59.676185+00:00
-- url     : https://prove2.me/submissions/49b56551-0e0d-45b3-85c2-5c41ce3b7143

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false
theorem solution (mode : ℕ) (hm : mode ∈ [0, 1, 2]) : lowerEarlyTerminalRequirementBinding lowerEarlyTerminalState2 mode := by
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl | rfl | rfl
  · unfold lowerEarlyTerminalRequirementBinding
    decide +kernel
  · unfold lowerEarlyTerminalRequirementBinding
    decide +kernel
  · unfold lowerEarlyTerminalRequirementBinding
    decide +kernel
#print axioms solution
