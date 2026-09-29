-- Prove2me | solution 2 for Freiman.lower_initial_bridge_A0
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:53:47.641413+00:00
-- url     : https://prove2.me/submissions/6a372a2d-7714-4c22-ad7b-958c5921d173

import Definitions.Def_Freiman_lowerBridgeCatalog
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_bridge_good

open Freiman

-- `lower_bridge_good` is stated for an arbitrary bridge case with the `n = 0` side
-- condition; instantiating it at `.aZero` (the zero case of the `.A` family) gives the
-- `A 0` bridge directly.
theorem solution : lowerBridgeGood .A 0 := by
  have h := lower_bridge_good .aZero 0
    (by simp [lowerBridgeZero, lowerBridgeSeamCase, lowerInitialSeamZero])
    (by simp [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily])
  simpa [lowerBridgeFamily, lowerBridgeSeamCase, lowerInitialSeamFamily] using h
