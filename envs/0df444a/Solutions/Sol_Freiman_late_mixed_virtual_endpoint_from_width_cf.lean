-- Prove2me | solution 1 for Freiman.late_mixed_virtual_endpoint_from_width_cf
-- status  : ACCEPTED   (prove)
-- author  : @Koki Yamada
-- created : 2026-09-16T09:39:43.270286+00:00
-- url     : https://prove2.me/submissions/30e9c5d2-38c6-4677-9f1b-35ad9cd69827

import Theorems.Thm_Freiman_late_mixed_virtual_represented
import Theorems.Thm_Freiman_late_mixed_virtual_holding_unique
open Freiman
set_option autoImplicit false

-- Existence of a holding mixed virtual case, plus uniqueness of its tails.
theorem solution
    (hcf : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z →
      certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z))
    (hw : LowerHistoryWidthLaw) (p : LowerPair) (e : LateEndpoint)
    (hm : lateMatches p e.right3)
    (hne1 : e.words.1 ≠ []) (hne2 : e.words.2 ≠ [])
    (hv : lateEndpointValid lateCatalog e)
    (hp : lowerHistoryWordParity (lateContext e.right3) e.words false ≠
      lowerHistoryWordParity (lateContext e.right3) e.words true)
    (hvirt : e.upper = ! lowerHistoryWordParity (lateContext e.right3) e.words
      (decide (¬ lowerWidth ((lowerNormalize p).2 ++ e.words.2) ≤
        lowerWidth ((lowerNormalize p).1 ++ e.words.1)))) :
    ∀ ids ∈ e.modes,
      lateHolds (lateBounds lateCatalog ids) (lateR p) (lateS p) (lateQ p) →
      lateActualEndpoint p e.words e.upper = lateActualValue p e.value := by
  intro ids hids hholds
  obtain ⟨z, cs, hmem, hat, hval⟩ :=
    late_mixed_virtual_represented hcf hw p e hm hne1 hne2 hp hvirt
  obtain ⟨_, _, _, hmode⟩ := hv
  obtain ⟨_, ⟨cs', hmem', hfin⟩⟩ := hmode ids hids
  have hat' : lowerHistoryAtBase (lowerNormalize p) cs' := by
    intro b hb
    have hbF : b ∈ cs'.toFinset := (List.mem_toFinset (l := cs')).mpr hb
    rw [hfin] at hbF
    have hbB : b ∈ lateBounds lateCatalog ids :=
      (List.mem_toFinset (l := lateBounds lateCatalog ids)).mp hbF
    simpa [lateHolds, lateR, lateS, lateQ, lowerHistoryAtBase,
      lowerHistoryConditions] using hholds b hbB
  have hz : z = e.value :=
    late_mixed_virtual_holding_unique hw p e hm hp hvirt z e.value cs cs'
      hmem hmem' hat hat'
  rw [hval, hz]
