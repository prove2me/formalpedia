-- Prove2me | solution 1 for Freiman.lower_guard_catalog
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T11:01:43.178951+00:00
-- url     : https://prove2.me/submissions/7fd5d7d3-5558-43e7-bb1b-f0cbe67aa281

import Definitions.Def_Freiman_lowerWordGuardData
import Mathlib.Data.List.Basic

open Freiman

set_option maxRecDepth 10000
set_option maxHeartbeats 0

-- `lowerGuardCatalogValid` is a conjunction of four concrete facts about the literal
-- catalogue: the printed-row count, the expanded case count, the total number of label
-- entries, and the agreement between the printed rows expanded one way and the case list
-- built the other. Every component is a computation over concrete lists, so unfolding the
-- definition leaves a decidable proposition that the kernel can evaluate directly.
theorem solution : lowerGuardCatalogValid := by
  unfold lowerGuardCatalogValid
  decide +kernel
