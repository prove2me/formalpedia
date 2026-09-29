-- Prove2me | solution 1 for Freiman.late_mixed_endpoint_from_width_cf
-- status  : ACCEPTED   (prove)
-- author  : @Koki Yamada
-- created : 2026-09-16T08:55:32.606505+00:00
-- url     : https://prove2.me/submissions/215aa7e8-d949-4bc6-a7be-a38ebeb2a1b6

import Theorems.Thm_Freiman_late_mixed_virtual_endpoint_from_width_cf
import Theorems.Thm_Freiman_late_mixed_natural_endpoint_from_width_cf
open Freiman
set_option autoImplicit false

-- Split mixed word-parity on the virtual-upper test of the holding width orientation.
theorem solution
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (hw : LowerHistoryWidthLaw) (p : LowerPair) (e : LateEndpoint)
    (hm : lateMatches p e.right3)
    (hne1 : e.words.1 ≠ []) (hne2 : e.words.2 ≠ [])
    (hv : lateEndpointValid lateCatalog e)
    (hp : lowerHistoryWordParity (lateContext e.right3) e.words false ≠
      lowerHistoryWordParity (lateContext e.right3) e.words true) :
    ∀ ids ∈ e.modes,
      lateHolds (lateBounds lateCatalog ids) (lateR p) (lateS p) (lateQ p) →
      lateActualEndpoint p e.words e.upper = lateActualValue p e.value := by
  intro ids hids hholds
  let wide : Bool :=
    decide (¬ lowerWidth ((lowerNormalize p).2 ++ e.words.2) ≤
      lowerWidth ((lowerNormalize p).1 ++ e.words.1))
  by_cases hvirt : e.upper =
      ! lowerHistoryWordParity (lateContext e.right3) e.words wide
  · exact late_mixed_virtual_endpoint_from_width_cf hcf hw p e hm hne1 hne2 hv hp
      hvirt ids hids hholds
  · exact late_mixed_natural_endpoint_from_width_cf hcf hw p e hm hne1 hne2 hv hp
      hvirt ids hids hholds
