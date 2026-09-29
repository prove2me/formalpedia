-- Prove2me | solution 1 for Freiman.lower_initial_bridge_An
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:17:32.250542+00:00
-- url     : https://prove2.me/submissions/ff41740e-9771-46a4-8422-2451bdf9b8b6

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

import Theorems.Thm_Freiman_lower_bridge_good

open Freiman

theorem solution (n : ℕ) (hn : 0 < n) : lowerBridgeGood .A n := by
  exact Freiman.lower_bridge_good .aPos n (by simp [lowerBridgeZero, lowerBridgeSeamCase, lowerInitialSeamZero, Nat.ne_of_gt hn]) (by decide)
