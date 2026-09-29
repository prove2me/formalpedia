-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_cover_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:04:21.703275+00:00
-- url     : https://prove2.me/submissions/203a82b1-f950-4418-b32d-d177c4880e42

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_order

open Freiman

theorem solution (p : LowerPair) : (lowerCover p).Nonempty := by
  exact ⟨lowerEndpoint p false, le_rfl, lowerEarlyTerminal_endpoint_order p⟩
