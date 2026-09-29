-- Prove2me | solution 2 for Freiman.lowerEarlyTerminal_cover_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T07:02:29.929421+00:00
-- url     : https://prove2.me/submissions/6d0a9501-e8a7-4a50-bf8a-488d7b15d680

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_order

open Freiman

theorem solution (p : LowerPair) : (lowerCover p).Nonempty := by
  unfold lowerCover
  exact Set.nonempty_Icc.mpr (lowerEarlyTerminal_endpoint_order p)
