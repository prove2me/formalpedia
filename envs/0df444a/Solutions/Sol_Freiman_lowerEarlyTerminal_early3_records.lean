-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_early3_records
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T16:09:29.220555+00:00
-- url     : https://prove2.me/submissions/5e67621d-bd3e-4f1a-84a1-2de89d0862e6

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic
open Freiman
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option linter.all false

theorem solution : ∀ r ∈ lowerEarlyTerminalEarly3.records, lowerEarlyTerminalRecordValid lowerEarlyTerminalEarly3 r := by
  unfold lowerEarlyTerminalRecordValid
  dsimp [lowerEarlyTerminalEarly3]
  decide +kernel

#print axioms solution
