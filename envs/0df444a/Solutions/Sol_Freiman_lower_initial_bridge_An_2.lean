-- Prove2me | solution 2 for Freiman.lower_initial_bridge_An
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:53:51.68533+00:00
-- url     : https://prove2.me/submissions/b55757c7-f19c-401e-8a30-33be29634053

import Definitions.Def_Freiman_lowerBridgeCatalog
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_bridge_good

open Freiman

-- The positive-`n` `.A` bridges come from the `.aPos` bridge case: its `lowerBridgeZero`
-- is `false`, matching `decide (n = 0) = false` for `0 < n`.
theorem solution (n : ℕ) (hn : 0 < n) : lowerBridgeGood .A n := by
  have h := lower_bridge_good .aPos n
    (by
      have hn0 : ¬ (n = 0) := by omega
      simp [lowerBridgeZero, lowerBridgeSeamCase, lowerInitialSeamZero, hn0])
    (by simp [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily])
  simpa [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily] using h
