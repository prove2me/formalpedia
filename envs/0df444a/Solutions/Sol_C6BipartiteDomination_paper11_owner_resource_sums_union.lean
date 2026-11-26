-- Prove2me | solution 1 for C6BipartiteDomination.paper11_owner_resource_sums_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:44.586698+00:00
-- url     : https://prove2.me/submissions/7f0aa4f1-1612-4a23-a4ae-5f7c49994afc

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11K3_K4_right_disjoint

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11K3RightVertices G D hCan hmax,
      paper11OwnerResource G D hCan hmax u) +
      ∑ u ∈ paper11K4RightVertices G D hCan hmax,
        paper11OwnerResource G D hCan hmax u =
      ∑ u ∈ paper11AllRepairOwners G D hCan hmax,
        paper11OwnerResource G D hCan hmax u := by
  classical
  rw [paper11AllRepairOwners, Finset.sum_union
    (paper11K3_K4_right_disjoint G hCan hmax)]
end C6BipartiteDomination
