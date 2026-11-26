-- Prove2me | solution 1 for C6BipartiteDomination.paper11OwnerCompensation_eq_K3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:09:13.337731+00:00
-- url     : https://prove2.me/submissions/fc45207f-ee2e-44a6-b11a-39d1ff828b34

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11K3_negative_incident_eq

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K3RightVertices G D hCan hmax) :
    paper11OwnerCompensation G D hCan hmax u =
      paper11K3Compensation G D hCan hmax u := by
  simp [paper11OwnerCompensation, paper11K3Compensation,
    paper11K3IncidentSupports, paper11K3Supports, paper11NegativeSupports,
    paper11K3_negative_incident_eq G hCan hmax hu]
end C6BipartiteDomination
