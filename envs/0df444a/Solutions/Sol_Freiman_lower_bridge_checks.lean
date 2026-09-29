-- Prove2me | solution 1 for Freiman.lower_bridge_checks
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:08:02.320848+00:00
-- url     : https://prove2.me/submissions/49ca6c50-56b0-4673-bde2-54e325eb462c

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

import Theorems.Thm_Freiman_lower_bridge_check_aZero
import Theorems.Thm_Freiman_lower_bridge_check_aPos
import Theorems.Thm_Freiman_lower_bridge_check_bZero
import Theorems.Thm_Freiman_lower_bridge_check_bPos
import Theorems.Thm_Freiman_lower_bridge_check_cZero
import Theorems.Thm_Freiman_lower_bridge_check_cPos

open Freiman

theorem solution (c : LowerBridgeCase) : ∀ r ∈ lowerBridgeRecords c, lowerBridgeChecked r := by
  cases c with
  | aZero => exact Freiman.lower_bridge_check_aZero
  | aPos => exact Freiman.lower_bridge_check_aPos
  | bZero => exact Freiman.lower_bridge_check_bZero
  | bPos => exact Freiman.lower_bridge_check_bPos
  | cZero => exact Freiman.lower_bridge_check_cZero
  | cPos => exact Freiman.lower_bridge_check_cPos
