-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3AvailableResource_sum_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:05:14.819546+00:00
-- url     : https://prove2.me/submissions/6e7db3a3-bbe8-44f0-9249-bc1da4724c81

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_paper11K3SpecialBudget_bonus_sum

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11K3RightVertices G D hCan hmax,
      paper11K3AvailableResource G D hCan hmax u) =
      (∑ u ∈ paper11K3RightVertices G D hCan hmax,
        (vertexCharge G D u +
          ∑ q ∈ paper11K3Compensation G D hCan hmax u,
            externalCharge G D q)) +
      7 * ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ) := by
  classical
  simp only [paper11K3AvailableResource, Finset.sum_add_distrib]
  rw [paper11K3SpecialBudget_bonus_sum G hCan hmax]
end C6BipartiteDomination
