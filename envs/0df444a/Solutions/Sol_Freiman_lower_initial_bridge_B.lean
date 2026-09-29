-- Prove2me | solution 1 for Freiman.lower_initial_bridge_B
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:17:47.873042+00:00
-- url     : https://prove2.me/submissions/afa44669-2041-4493-bc43-4341bb170273

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

import Theorems.Thm_Freiman_lower_bridge_good

open Freiman

theorem solution (n : ℕ) : lowerBridgeGood .B n := by
  cases n with
  | zero => exact Freiman.lower_bridge_good .bZero 0 rfl (by decide)
  | succ n => exact Freiman.lower_bridge_good .bPos (n+1) (by simp [lowerBridgeZero, lowerBridgeSeamCase, lowerInitialSeamZero]) (by decide)
