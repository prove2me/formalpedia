-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_fork_ranges
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:38:57.615123+00:00
-- url     : https://prove2.me/submissions/330792b8-bd59-4efc-bcbe-bccea02210ad

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false
private instance decForkExceptional (c : LowerEarlyTerminalForkCase) : Decidable (lowerEarlyTerminalForkExceptional c) := by
  unfold lowerEarlyTerminalForkExceptional
  infer_instance
private instance decForkRangeExcluded (c : LowerEarlyTerminalForkCase) : Decidable (lowerEarlyTerminalForkRangeExcluded c) := by
  unfold lowerEarlyTerminalForkRangeExcluded lowerEarlyTerminalRangesApart
  infer_instance
theorem solution : lowerEarlyTerminalForkRangesValid := by
  unfold lowerEarlyTerminalForkRangesValid
  decide +kernel
#print axioms solution
