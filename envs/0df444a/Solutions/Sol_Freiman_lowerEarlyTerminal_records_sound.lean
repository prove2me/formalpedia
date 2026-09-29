-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_records_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:04:53.22852+00:00
-- url     : https://prove2.me/submissions/9f80f75f-0644-4154-8e64-090291caecf3

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_pairs_sound
import Theorems.Thm_Freiman_lowerEarlyTerminal_record_sound

open Freiman

theorem solution (C : LowerEarlyTerminalCatalog) (hv : lowerEarlyTerminalFiniteValid C) : lowerEarlyTerminalRecordsSound C := by
  intro rec hr
  exact lowerEarlyTerminal_record_sound C (lowerEarlyTerminal_pairs_sound C hv.2.1) rec (hv.2.2.1 rec hr)
