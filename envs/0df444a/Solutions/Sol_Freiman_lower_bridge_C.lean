-- Prove2me | solution 1 for Freiman.lower_bridge_C
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:17:32.631726+00:00
-- url     : https://prove2.me/submissions/75e960bf-941f-4185-bc14-947a0d7a60d4

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

import Theorems.Thm_Freiman_lower_bridge_C_comparison
import Theorems.Thm_Freiman_lower_bridge_facts

open Freiman

theorem solution (c : LowerBridgeCase) (n k : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hf : lowerBridgeFamily c = .C) : lowerBridgeInterval .C n k 0 ⊆ lowerFamilyH .B n (k+2) 0 := by
  exact Freiman.lower_bridge_C_comparison c n k hc hf (Freiman.lower_bridge_facts c n k hc)
