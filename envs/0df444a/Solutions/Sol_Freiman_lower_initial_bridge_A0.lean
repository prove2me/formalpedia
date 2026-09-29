-- Prove2me | solution 1 for Freiman.lower_initial_bridge_A0
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:17:32.996814+00:00
-- url     : https://prove2.me/submissions/52de2d74-799c-45ea-8013-7e1b608cb0a4

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

import Theorems.Thm_Freiman_lower_bridge_good

open Freiman

theorem solution : lowerBridgeGood .A 0 := by
  exact Freiman.lower_bridge_good .aZero 0 rfl (by decide)
