-- Prove2me | solution 2 for Freiman.lower_initial_bridge_B
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:53:55.697751+00:00
-- url     : https://prove2.me/submissions/b22b51da-4771-48b0-baf5-d375c79ae4a9

import Definitions.Def_Freiman_lowerBridgeCatalog
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_bridge_good

open Freiman

-- The `B` bridges quantify over every `n`, so split at `n = 0` between the `.bZero` and
-- `.bPos` bridge cases; both land in the `.B` family.
theorem solution (n : ℕ) : lowerBridgeGood .B n := by
  by_cases h : n = 0
  · subst h
    have h0 := lower_bridge_good .bZero 0
      (by simp [lowerBridgeZero, lowerBridgeSeamCase, lowerInitialSeamZero])
      (by simp [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily])
    simpa [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily] using h0
  · have h0 := lower_bridge_good .bPos n
      (by
        have hn0 : ¬ (n = 0) := h
        simp [lowerBridgeZero, lowerBridgeSeamCase, lowerInitialSeamZero, hn0])
      (by simp [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily])
    simpa [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily] using h0
