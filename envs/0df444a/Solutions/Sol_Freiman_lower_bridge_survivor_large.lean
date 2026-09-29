-- Prove2me | solution 1 for Freiman.lower_bridge_survivor_large
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:17:47.757324+00:00
-- url     : https://prove2.me/submissions/2012413a-6922-4e68-b8f0-820300dc8a39

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

import Theorems.Thm_Freiman_lower_bridge_facts
import Theorems.Thm_Freiman_lower_bridge_survivor_extract

open Freiman

theorem solution (c : LowerBridgeCase) (n k : ℕ) (hc : lowerBridgeZero c = decide (n=0)) : lowerBridgeSurvivorLarge c n k := by
  exact Freiman.lower_bridge_survivor_extract c n k hc (Freiman.lower_bridge_facts c n k hc)
