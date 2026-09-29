-- Prove2me | solution 2 for Freiman.lowerEarlyTerminal_all_terminal_requirements
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T06:04:38.831613+00:00
-- url     : https://prove2.me/submissions/1169a778-d8c9-4d05-b886-e5c6096f3781

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_requirements
import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_requirements
import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_requirements
import Mathlib.Tactic.FinCases

open Freiman

theorem solution (i : Fin 3) :
    lowerEarlyTerminalRequirementBinding
      (lowerEarlyTerminalTerminalCatalog i) 2 := by
  fin_cases i
  · exact lowerEarlyTerminal_state1_requirements 2 (by decide)
  · exact lowerEarlyTerminal_state2_requirements 2 (by decide)
  · exact lowerEarlyTerminal_terminal3_requirements 2 (by decide)
