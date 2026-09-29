-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_catalog_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:04:52.939098+00:00
-- url     : https://prove2.me/submissions/dda7492f-8247-494d-a30a-27e42b626e84

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_records_sound
import Theorems.Thm_Freiman_lowerEarlyTerminal_coverage_sound

open Freiman

theorem solution (C : LowerEarlyTerminalCatalog) (hv : lowerEarlyTerminalFiniteValid C) : lowerEarlyTerminalGoalsSound C := by
  exact lowerEarlyTerminal_coverage_sound C hv.2.2.2 (lowerEarlyTerminal_records_sound C hv)
