-- Prove2me | solution 1 for Freiman.lower_bridge_numeric
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:08:17.282285+00:00
-- url     : https://prove2.me/submissions/d4b0c5a3-7d98-4716-93a8-cdcfe86ea8e1

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

import Theorems.Thm_Freiman_lower_bridge_bindings
import Theorems.Thm_Freiman_lower_bridge_checks
import Theorems.Thm_Freiman_lower_bridge_positive

open Freiman

theorem solution (c : LowerBridgeCase) (x y : ℝ) (hxy : certRectangleMem lowerBridgeRectangle x y) : lowerBridgeNumeric c x y := by
  intro r hr
  rw [← Freiman.lower_bridge_bindings c r hr x y]
  exact Freiman.lower_bridge_positive r (Freiman.lower_bridge_checks c r hr) x y hxy
