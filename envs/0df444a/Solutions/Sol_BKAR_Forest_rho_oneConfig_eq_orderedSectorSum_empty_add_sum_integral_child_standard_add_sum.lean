-- Prove2me | solution 1 for BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_integral_child_standard_add_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:32:33.565295+00:00
-- url     : https://prove2.me/submissions/7c3dc7bd-d925-4066-975a-a7969c64a6b8

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_sum_allBranchesBoundaryExpansion
import Theorems.Thm_BKAR_Forest_integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_sum
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


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
        Finset.sum (Forest.empty V).activeEdges.attach
          (fun e => ∫ t in 0..(1 : ℝ),
            (mixedPartialList [e.val].reverse ρ
              ((choices (Forest.empty V) e).forest.standardInterp
                ((choices (Forest.empty V) e).forest.paramsOfOrder
                  [e.val] [t])) +
            Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                  (choices ((choices (Forest.empty V) e).forest) e').forest
                  ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))) := by
  rw [rho_oneConfig_eq_orderedSectorSum_empty_add_sum_allBranchesBoundaryExpansion
    choices ρ hanalytic]
  apply congrArg
    (fun r => (Forest.empty V).orderedSectorSum ρ + r)
  apply Finset.sum_congr rfl
  intro e _
  exact
    integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_sum
      choices (Forest.empty V) e [] [] 1 ρ
end BKAR.Forest
