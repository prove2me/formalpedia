-- Prove2me | solution 1 for BKAR.Forest.rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:00.832998+00:00
-- url     : https://prove2.me/submissions/32e72e47-526b-4b39-a23c-9dd69bb350b8

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeContribution_eq_sum_treeFiber_of_activeEdges_card_le
import Theorems.Thm_BKAR_Forest_sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber
import Theorems.Thm_BKAR_Forest_orderedSectorSum_empty
import Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_boundarySupportOrderTreeContribution


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ)
    (hfiber :
      boundarySupportOrderTreeFiberIntegrable choices
        (Forest.empty V).activeEdges.card (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            rootBoundarySupportOrderContribution choices ρ I order)) := by
  rw [rho_oneConfig_eq_orderedSectorSum_empty_add_boundarySupportOrderTreeContribution
    choices ρ hanalytic]
  rw [orderedSectorSum_empty]
  rw [boundarySupportOrderTreeContribution_eq_sum_treeFiber_of_activeEdges_card_le
    choices (Forest.empty V).activeEdges.card (Forest.empty V) [] [] 1 ρ
    le_rfl hfiber]
  rw [← sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber
    choices ρ]
end BKAR.Forest
