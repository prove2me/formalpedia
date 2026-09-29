-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_terminal_ready
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:06:10.989758+00:00
-- url     : https://prove2.me/submissions/574432b8-d2ba-4d49-86d8-e1cb51f1dee0

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_parameter_laws
import Theorems.Thm_Freiman_lowerEarlyTerminal_domain_ready
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal_applicability
import Theorems.Thm_Freiman_lowerEarlyTerminal_required_sound
import Theorems.Thm_Freiman_lowerEarlyTerminal_all_terminal_finite
import Theorems.Thm_Freiman_lowerEarlyTerminal_all_terminal_requirements
import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal_geometry

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (h27 : ¬ lowerA p 27) (h34 : ¬ lowerA p 34) (i : Fin 3)
    (he : lowerEnds (lowerNormalize p).1 (lowerEarlyTerminalTerminalCatalog i).leftContext) :
    lowerEarlyTerminalListGeometry p (lowerEarlyTerminalTerminal (lowerEarlyTerminalPrimary p)) := by
  have hi := lowerEarlyTerminal_terminal_applicability lowerEarlyTerminal_parameter_laws
    lowerEarlyTerminal_domain_ready lowerHistory_width_threshold t p hs hd h27 h34 i he
  exact lowerEarlyTerminal_terminal_geometry (lowerEarlyTerminalTerminalCatalog i) t p hs hd h27 h34
    (lowerEarlyTerminal_required_sound _ p 2 hi.1 hi.2.1
      (lowerEarlyTerminal_all_terminal_finite i) (lowerEarlyTerminal_all_terminal_requirements i)) hi.2.2
