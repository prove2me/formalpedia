-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_terminal3_requirements
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:39:00.396433+00:00
-- url     : https://prove2.me/submissions/e96991d3-3e73-4b1d-8184-1d96e10771bf

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false
theorem solution (mode : ℕ) (hm : mode ∈ [2]) : lowerEarlyTerminalRequirementBinding lowerEarlyTerminalTerminal3 mode := by
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl
  · unfold lowerEarlyTerminalRequirementBinding
    decide +kernel
#print axioms solution
