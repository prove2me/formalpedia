-- Prove2me | solution 2 for Freiman.lowerHistory_endpoint_semantics
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T05:22:32.089981+00:00
-- url     : https://prove2.me/submissions/467720be-db53-49f9-925e-d7103f859d59

import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lowerHistory_equal_endpoint_cases
import Theorems.Thm_Freiman_lowerHistory_mixed_endpoint_cases
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Theorems.Thm_Freiman_lowerHistory_cf_value

open Freiman

theorem solution : LowerHistoryEndpointLaw := by
  have hwidth : LowerHistoryWidthLaw := by
    intro base words
    exact lowerHistory_width_threshold base words
  have hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z) := by
    intro w z hz
    exact lowerHistory_cf_value w z hz
  intro base C hc words upper
  by_cases hp : lowerHistoryWordParity C words false = lowerHistoryWordParity C words true
  · exact lowerHistory_equal_endpoint_cases hwidth hcf base C hc words upper hp
  · exact lowerHistory_mixed_endpoint_cases hwidth hcf base C hc words upper hp
