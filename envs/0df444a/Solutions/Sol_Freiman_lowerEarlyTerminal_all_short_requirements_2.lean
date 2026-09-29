-- Prove2me | solution 2 for Freiman.lowerEarlyTerminal_all_short_requirements
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T06:38:29.08609+00:00
-- url     : https://prove2.me/submissions/fca6f5e3-94f4-4422-b292-a87d8d99d703

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Theorems.Thm_Freiman_lowerEarlyTerminal_early3_requirements
import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_requirements
import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_requirements
import Mathlib.Tactic.FinCases

open Freiman

theorem solution (i : Fin 3) (mode : ℕ) (hm : mode < 2) :
    lowerEarlyTerminalRequirementBinding
      (lowerEarlyTerminalShortCatalog i) mode := by
  have hmode : mode = 0 ∨ mode = 1 := by omega
  rcases hmode with rfl | rfl <;> fin_cases i
  · exact lowerEarlyTerminal_early3_requirements 0 (by decide)
  · exact lowerEarlyTerminal_state2_requirements 0 (by decide)
  · exact lowerEarlyTerminal_state1_requirements 0 (by decide)
  · exact lowerEarlyTerminal_early3_requirements 1 (by decide)
  · exact lowerEarlyTerminal_state2_requirements 1 (by decide)
  · exact lowerEarlyTerminal_state1_requirements 1 (by decide)
