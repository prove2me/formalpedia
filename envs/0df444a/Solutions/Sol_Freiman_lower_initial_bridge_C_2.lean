-- Prove2me | solution 2 for Freiman.lower_initial_bridge_C
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T04:07:57.559101+00:00
-- url     : https://prove2.me/submissions/e46d1d17-d01a-4f88-a325-36c96771650c

import Definitions.Def_Freiman_lowerBridgeModel
import Theorems.Thm_Freiman_lower_bridge_C

open Freiman

theorem solution (n k : ℕ) :
    lowerBridgeInterval .C n k 0 ⊆ lowerFamilyH .B n (k+2) 0 := by
  by_cases hn : n = 0
  · subst n
    exact lower_bridge_C .cZero 0 k (by decide) (by rfl)
  · have hc : lowerBridgeZero .cPos = decide (n = 0) := by
      simp [lowerBridgeZero, lowerBridgeSeamCase, lowerInitialSeamZero, hn]
    have hf : lowerBridgeFamily .cPos = .C := by
      rfl
    exact lower_bridge_C .cPos n k hc hf
