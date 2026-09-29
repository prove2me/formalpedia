-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_state1_finite
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:04:38.463612+00:00
-- url     : https://prove2.me/submissions/5b1d45a1-2bd5-4000-85df-0f6de985ba1e

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_goal_ids
import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_pairs
import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_records
import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_coverage

open Freiman

theorem solution : lowerEarlyTerminalFiniteValid lowerEarlyTerminalState1 := by
  exact ⟨lowerEarlyTerminal_state1_goal_ids, lowerEarlyTerminal_state1_pairs, lowerEarlyTerminal_state1_records, lowerEarlyTerminal_state1_coverage⟩
