-- Prove2me | solution 1 for Freiman.lower_bridge_bindings
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:08:01.69819+00:00
-- url     : https://prove2.me/submissions/d70d50e0-14d0-4d53-987b-bb0b8ad3187d

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

import Theorems.Thm_Freiman_lower_bridge_binding_aZero
import Theorems.Thm_Freiman_lower_bridge_binding_aPos
import Theorems.Thm_Freiman_lower_bridge_binding_bZero
import Theorems.Thm_Freiman_lower_bridge_binding_bPos
import Theorems.Thm_Freiman_lower_bridge_binding_cZero
import Theorems.Thm_Freiman_lower_bridge_binding_cPos

open Freiman

theorem solution (c : LowerBridgeCase) : ∀ r ∈ lowerBridgeRecords c, ∀ x y : ℝ, certPolyEval r.polynomial x y = lowerBridgeNumerator c r x y := by
  cases c with
  | aZero => exact Freiman.lower_bridge_binding_aZero
  | aPos => exact Freiman.lower_bridge_binding_aPos
  | bZero => exact Freiman.lower_bridge_binding_bZero
  | bPos => exact Freiman.lower_bridge_binding_bPos
  | cZero => exact Freiman.lower_bridge_binding_cZero
  | cPos => exact Freiman.lower_bridge_binding_cPos
