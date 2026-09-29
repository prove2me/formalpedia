-- Prove2me | solution 1 for Freiman.late_endpoint_from_width_cf
-- status  : ACCEPTED   (prove)
-- author  : @Koki Yamada
-- created : 2026-09-16T01:19:40.669235+00:00
-- url     : https://prove2.me/submissions/f478f9e7-ec84-41de-bccf-316e9f5158d2

import Theorems.Thm_Freiman_late_equal_endpoint_from_width_cf
import Theorems.Thm_Freiman_late_mixed_endpoint_from_width_cf
open Freiman
set_option autoImplicit false

-- Split the selected-mode identity on word-parity equality in the source context.
theorem solution (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (hw : LowerHistoryWidthLaw) : lateEndpointLaw := by
  intro p e hm hne1 hne2 hv ids hids hholds
  by_cases hp : lowerHistoryWordParity (lateContext e.right3) e.words false =
      lowerHistoryWordParity (lateContext e.right3) e.words true
  · exact late_equal_endpoint_from_width_cf hcf hw p e hm hne1 hne2 hv hp ids hids hholds
  · exact late_mixed_endpoint_from_width_cf hcf hw p e hm hne1 hne2 hv hp ids hids hholds
