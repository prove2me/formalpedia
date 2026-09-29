-- Prove2me | solution 1 for Freiman.lower_bridge_cover_order
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:17:31.443791+00:00
-- url     : https://prove2.me/submissions/e40759fa-1fab-4bb3-8176-8097600f7423

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_order

open Freiman

theorem solution (c : LowerBridgeCase) (n : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hf : lowerBridgeFamily c ≠ .C) : ∀ d ∈ lowerBridgeLabels (lowerBridgeFamily c) n, lowerEndpoint (lowerPhysicalAdd (lowerFamilyPair (lowerBridgeFamily c) n 0 0) d) false ≤ lowerEndpoint (lowerPhysicalAdd (lowerFamilyPair (lowerBridgeFamily c) n 0 0) d) true := by
  intro d hd
  exact Freiman.lowerEarlyTerminal_endpoint_order _
