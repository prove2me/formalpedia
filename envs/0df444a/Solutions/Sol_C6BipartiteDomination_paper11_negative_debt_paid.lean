-- Prove2me | solution 1 for C6BipartiteDomination.paper11_negative_debt_paid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:46.765872+00:00
-- url     : https://prove2.me/submissions/097669ff-642c-468b-aad9-9a07296156af

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11K4_total_debt_bound
import Theorems.Thm_C6BipartiteDomination_paper11_negative_debt_split
import Theorems.Thm_C6BipartiteDomination_paper11OwnerResource_sum_decomposition
import Theorems.Thm_C6BipartiteDomination_paper11_owner_resource_sums_union
import Theorems.Thm_C6BipartiteDomination_paper11K3_base_resource_eq_owner
import Theorems.Thm_C6BipartiteDomination_paper11K4_resource_eq_owner
import Theorems.Thm_C6BipartiteDomination_paper11K3AvailableResource_sum_decomposition
import Theorems.Thm_C6BipartiteDomination_paper11K3SpecialBudget_cost_bound
import Theorems.Thm_C6BipartiteDomination_paper11_chosen_k3_charge_balance


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (hNoIso : HasNoIsolatedVertices G) :
    (∑ w ∈ paper11NegativeSupports G D, -externalCharge G D w) ≤
      (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
        vertexCharge G D u) +
      (∑ q ∈ paper11AllCompensation G D hCan hmax,
        externalCharge G D q) +
      7 * ((incidenceTotal G D - (Z0Part G D).card : ℕ) : ℤ) := by
  classical
  have hK3 := paper11_chosen_k3_charge_balance G hCan hmax
  have hK4 := paper11K4_total_debt_bound G hCan hmax
  have hsplit := paper11_negative_debt_split G hCan hmax
  have hK3base := paper11K3_base_resource_eq_owner G hCan hmax
  have hK4base := paper11K4_resource_eq_owner G hCan hmax
  have hOwnerUnion := paper11_owner_resource_sums_union G hCan hmax
  have hOwnerDecomp := paper11OwnerResource_sum_decomposition G hCan hmax
  have hAvailable := paper11K3AvailableResource_sum_decomposition G hCan hmax
  have hSpecial := paper11K3SpecialBudget_cost_bound G hCan hmax hNoIso
  calc
    (∑ w ∈ paper11NegativeSupports G D, -externalCharge G D w) =
        (∑ w ∈ paper11K3Supports G D, -externalCharge G D w) +
          ∑ w ∈ paper11K4Supports G D, -externalCharge G D w := hsplit
    _ ≤ (∑ u ∈ paper11K3RightVertices G D hCan hmax,
          paper11K3AvailableResource G D hCan hmax u) +
        ∑ u ∈ paper11K4RightVertices G D hCan hmax,
          paper11K4Resource G D hCan hmax u := add_le_add hK3 hK4
    _ = ((∑ u ∈ paper11K3RightVertices G D hCan hmax,
          (vertexCharge G D u +
            ∑ q ∈ paper11K3Compensation G D hCan hmax u,
              externalCharge G D q)) +
          7 * ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ)) +
        ∑ u ∈ paper11K4RightVertices G D hCan hmax,
          paper11K4Resource G D hCan hmax u := by rw [hAvailable]
    _ = ((∑ u ∈ paper11K3RightVertices G D hCan hmax,
          paper11OwnerResource G D hCan hmax u) +
          ∑ u ∈ paper11K4RightVertices G D hCan hmax,
            paper11OwnerResource G D hCan hmax u) +
          7 * ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ) := by
        rw [hK3base, hK4base]
        ring
    _ = (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
          paper11OwnerResource G D hCan hmax u) +
          7 * ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ) := by
        rw [hOwnerUnion]
    _ = (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
          vertexCharge G D u) +
          ∑ q ∈ paper11AllCompensation G D hCan hmax,
            externalCharge G D q +
          7 * ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ) := by
        rw [hOwnerDecomp]
    _ ≤ (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
          vertexCharge G D u) +
          ∑ q ∈ paper11AllCompensation G D hCan hmax,
            externalCharge G D q +
          7 * ((incidenceTotal G D - (Z0Part G D).card : ℕ) : ℤ) := by
        linarith
end C6BipartiteDomination
