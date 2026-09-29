-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_state2_finite
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:04:37.930576+00:00
-- url     : https://prove2.me/submissions/36c9ffd6-4f26-4a7c-b616-77ff93a2c32a

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_goal_ids
import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_pairs
import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_records
import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_coverage

open Freiman

theorem solution : lowerEarlyTerminalFiniteValid lowerEarlyTerminalState2 := by
  exact ⟨lowerEarlyTerminal_state2_goal_ids, lowerEarlyTerminal_state2_pairs, lowerEarlyTerminal_state2_records, lowerEarlyTerminal_state2_coverage⟩
