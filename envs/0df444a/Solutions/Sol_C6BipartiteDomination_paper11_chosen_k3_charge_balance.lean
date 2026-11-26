-- Prove2me | solution 1 for C6BipartiteDomination.paper11_chosen_k3_charge_balance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:09:57.656338+00:00
-- url     : https://prove2.me/submissions/2af618c1-3490-4139-b0c7-4a703fbc9863

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_paper11_pure_k3_charge_balance
import Theorems.Thm_C6BipartiteDomination_paper11K3Edges_subset_product
import Theorems.Thm_C6BipartiteDomination_paper11K3_left_degree_profile
import Theorems.Thm_C6BipartiteDomination_paper11K3_left_debt_bound
import Theorems.Thm_C6BipartiteDomination_paper11K3_right_degree_profile
import Theorems.Thm_C6BipartiteDomination_paper11K3_right_resource_bound

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ w ∈ paper11K3Supports G D, -externalCharge G D w) ≤
      ∑ u ∈ paper11K3RightVertices G D hCan hmax,
        paper11K3AvailableResource G D hCan hmax u := by
  classical
  apply paper11_pure_k3_charge_balance
    (paper11K3Supports G D) (paper11K3RightVertices G D hCan hmax)
    (paper11K3Edges G D hCan hmax)
    (paper11K3Edges_subset_product G hCan hmax)
    (fun w => -externalCharge G D w)
    (paper11K3AvailableResource G D hCan hmax)
  · intro w hw
    exact paper11K3_left_degree_profile G hCan hmax hw
  · intro u hu
    exact paper11K3_right_degree_profile G hCan hmax hu
  · intro w hw
    exact paper11K3_left_debt_bound G hCan hmax hw
  · intro u hu
    exact paper11K3_right_resource_bound G hCan hmax hu
end C6BipartiteDomination
