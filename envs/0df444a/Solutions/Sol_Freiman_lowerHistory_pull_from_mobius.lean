-- Prove2me | solution 1 for Freiman.lowerHistory_pull_from_mobius
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T05:48:28.244447+00:00
-- url     : https://prove2.me/submissions/0cb233bd-05f8-4537-9a3d-2897bbf75ac7

import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lowerHistory_pull_value

open Freiman

theorem solution
    (_hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (_hinv : ∀ z : CertField, certFieldVal z ≠ 0 →
      certFieldVal (lowerHistoryInv z) = (certFieldVal z)⁻¹) :
    LowerHistoryPullLaw := by
  exact lowerHistory_pull_value
