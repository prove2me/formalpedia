-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3_base_resource_eq_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:10:17.490061+00:00
-- url     : https://prove2.me/submissions/626a1cca-dfec-4917-9a67-6c3002188d70

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11OwnerCompensation_eq_K3

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
      (vertexCharge G D u +
        ∑ q ∈ paper11K3Compensation G D hCan hmax u,
          externalCharge G D q)) =
      ∑ u ∈ paper11K3RightVertices G D hCan hmax,
        paper11OwnerResource G D hCan hmax u := by
  apply Finset.sum_congr rfl
  intro u hu
  unfold paper11OwnerResource
  rw [paper11OwnerCompensation_eq_K3 G hCan hmax hu]
end C6BipartiteDomination
