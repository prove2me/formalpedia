-- Prove2me | solution 1 for Freiman.lower_h5_local_endpoint_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T04:20:19.213179+00:00
-- url     : https://prove2.me/submissions/db747efd-5dbd-4d28-b938-e0a9e9e019aa

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem solution (ho : ∀ p : LowerPair, lowerEndpoint p false ≤ lowerEndpoint p true)
    (p : LowerPair) (l : LowerLabel) : lowerLocalLower p l ≤ lowerH5LocalUpper p l := by
  unfold lowerLocalLower lowerH5LocalUpper
  by_cases h : (lowerNormalize p).1.length % 2 = 0
  · simp [h]
    exact ho (lowerChild p l)
  · simp [h]
    have h' := ho (lowerChild p l)
    linarith
