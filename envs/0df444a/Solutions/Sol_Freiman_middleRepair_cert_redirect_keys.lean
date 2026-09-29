-- Prove2me | solution 1 for Freiman.middleRepair_cert_redirect_keys
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T09:35:45.714343+00:00
-- url     : https://prove2.me/submissions/5f475b96-1f54-4350-9e88-eb027c0666f6

import Definitions.Def_Freiman_middleRepairLedger

open Freiman

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace M8Sep10RedirectKeys

private def selected : List MiddleCertRecord := [
  ⟨1,24,[-1],917⟩,
  ⟨1,29,[-1],917⟩,
  ⟨11,4,[24,25,26,27,28,29,30,31],917⟩,
  ⟨11,6,[24,25,26,27,28,29,30,31],917⟩,
  ⟨92,2,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,
  ⟨92,3,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,
  ⟨92,4,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,
  ⟨92,5,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,
  ⟨92,6,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,
  ⟨92,7,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,
  ⟨96,8,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,
  ⟨96,9,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩]

private theorem selected_mem : ∀ r ∈ selected, r ∈ middleCertData.records := by
  decide +kernel

private theorem redirects_selected :
    ∀ a ∈ middleRepairRedirects, ∃ r ∈ selected,
      a.goal = r.goal ∧ a.branch = r.branch ∧ a.parent ∈ r.parents ∧
      a.originalProof = r.proof := by
  decide +kernel

end M8Sep10RedirectKeys

theorem solution :
    ∀ a ∈ middleRepairRedirects, ∃ rec ∈ middleCertData.records, a.goal=rec.goal ∧ a.branch=rec.branch ∧ a.parent∈rec.parents ∧ a.originalProof=rec.proof := by
  intro a ha
  obtain ⟨r, hr, hg, hb, hp, hproof⟩ := M8Sep10RedirectKeys.redirects_selected a ha
  exact ⟨r, M8Sep10RedirectKeys.selected_mem r hr, hg, hb, hp, hproof⟩

#print axioms solution
