-- Prove2me | solution 1 for BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_orderedContribution_add_sum_integral_child_sum_of_allBranchesAnalytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:55:21.340503+00:00
-- url     : https://prove2.me/submissions/44005ebb-e716-47f4-9917-1920d649c8e9

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_Forest_allBranchesAnalytic_child_standard_intervalIntegrable
import Theorems.Thm_BKAR_Forest_allBranchesAnalytic_child_recursive_sum_intervalIntegrable
import Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_sum_orderedContribution_add_sum_integral_child_sum

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
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        (Finset.sum (Forest.empty V).activeEdges.attach
          (fun e =>
            (choices (Forest.empty V) e).forest.orderedContribution
              [e.val] ρ) +
        Finset.sum (Forest.empty V).activeEdges.attach
          (fun e => ∫ t in 0..(1 : ℝ),
            Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                  (choices ((choices (Forest.empty V) e).forest) e').forest
                  ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))) := by
  exact
    rho_oneConfig_eq_orderedSectorSum_empty_add_sum_orderedContribution_add_sum_integral_child_sum
      choices ρ hanalytic
      (fun e =>
        allBranchesAnalytic.child_standard_intervalIntegrable
          choices (Forest.empty V) e [] [] 1 ρ hanalytic)
      (fun e =>
        allBranchesAnalytic.child_recursive_sum_intervalIntegrable
          choices (Forest.empty V) e [] [] 1 ρ hanalytic)
end BKAR.Forest
