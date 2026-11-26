-- Prove2me | solution 1 for BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_singleton_supportOrderContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:32:35.282806+00:00
-- url     : https://prove2.me/submissions/aa30d96f-9907-41b1-a58d-1cbdff227b35

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_singleton_branchIntegral_of_forall_child_activeEdges_eq_empty
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegral_empty_eq_sum_supportOrderContribution


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
    (hterm : ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
      (choices (Forest.empty V) e).forest.activeEdges = ∅) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              ActiveTerminalBranchData.supportOrderContribution
                (ActiveTerminalBranchData.singleton
                  (fun e => choices (Forest.empty V) e) hterm)
                I order ρ)) := by
  rw [rho_oneConfig_eq_orderedSectorSum_empty_add_singleton_branchIntegral_of_forall_child_activeEdges_eq_empty
    choices ρ hanalytic hterm]
  rw [ActiveTerminalBranchData.branchIntegral_empty_eq_sum_supportOrderContribution
    (ActiveTerminalBranchData.singleton
      (fun e => choices (Forest.empty V) e) hterm) ρ]
end BKAR.Forest
