-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_early3_requirements
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:38:58.260384+00:00
-- url     : https://prove2.me/submissions/c46f9b7d-ca97-4896-b1fe-ff6463246e0e

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false
theorem solution (mode : ℕ) (hm : mode ∈ [0, 1]) : lowerEarlyTerminalRequirementBinding lowerEarlyTerminalEarly3 mode := by
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl | rfl
  · unfold lowerEarlyTerminalRequirementBinding
    decide +kernel
  · unfold lowerEarlyTerminalRequirementBinding
    decide +kernel
#print axioms solution
