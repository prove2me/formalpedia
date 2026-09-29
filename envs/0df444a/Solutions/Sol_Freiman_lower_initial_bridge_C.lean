-- Prove2me | solution 1 for Freiman.lower_initial_bridge_C
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:17:47.669274+00:00
-- url     : https://prove2.me/submissions/b5b2fc00-e9d6-4264-a61c-301b83aa27da

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

import Theorems.Thm_Freiman_lower_bridge_C

open Freiman

theorem solution (n k : ℕ) : lowerBridgeInterval .C n k 0 ⊆ lowerFamilyH .B n (k+2) 0 := by
  cases n with
  | zero => exact Freiman.lower_bridge_C .cZero 0 k rfl rfl
  | succ n => exact Freiman.lower_bridge_C .cPos (n+1) k (by simp [lowerBridgeZero, lowerBridgeSeamCase, lowerInitialSeamZero]) rfl
