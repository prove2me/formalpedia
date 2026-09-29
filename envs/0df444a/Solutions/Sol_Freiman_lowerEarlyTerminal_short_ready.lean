-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_short_ready
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:06:12.139235+00:00
-- url     : https://prove2.me/submissions/c56df2c9-2da2-4b78-8415-5eb1e1b9003a

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_parameter_laws
import Theorems.Thm_Freiman_lowerEarlyTerminal_domain_ready
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Theorems.Thm_Freiman_lowerEarlyTerminal_short_applicability
import Theorems.Thm_Freiman_lowerEarlyTerminal_required_sound
import Theorems.Thm_Freiman_lowerEarlyTerminal_all_short_finite
import Theorems.Thm_Freiman_lowerEarlyTerminal_all_short_requirements
import Theorems.Thm_Freiman_lowerEarlyTerminal_short_geometry

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (mode : ℕ) (hm : mode<2)
    (hb : if mode=0 then lowerA p 27 else ¬ lowerA p 27 ∧ lowerA p 34) :
    lowerEarlyTerminalListGeometry p (if mode=0 then lowerEarlyTerminalFirst else lowerEarlyTerminalSecond) := by
  obtain ⟨i,hi⟩ := lowerEarlyTerminal_short_applicability lowerEarlyTerminal_parameter_laws
    lowerEarlyTerminal_domain_ready lowerHistory_width_threshold t p hs hd mode hm hb
  exact lowerEarlyTerminal_short_geometry (lowerEarlyTerminalShortCatalog i) t p hs hd mode hm hb
    (lowerEarlyTerminal_required_sound _ p mode hi.1 hi.2.1
      (lowerEarlyTerminal_all_short_finite i) (lowerEarlyTerminal_all_short_requirements i mode hm)) hi.2.2
