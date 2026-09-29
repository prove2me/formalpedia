-- Prove2me | solution 1 for Freiman.lowerHistory_cf_value
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:06:35.144027+00:00
-- url     : https://prove2.me/submissions/ba2477f6-69d0-41fe-bea9-09ebbacc47b9

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_cf_from_inverse
import Theorems.Thm_Freiman_lowerHistory_inv_value

open Freiman

theorem solution (w : List ℕ+) (z : CertField) (hz : 0 ≤ certFieldVal z) :
    certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z) := by
  exact lowerHistory_cf_from_inverse lowerHistory_inv_value w z hz
