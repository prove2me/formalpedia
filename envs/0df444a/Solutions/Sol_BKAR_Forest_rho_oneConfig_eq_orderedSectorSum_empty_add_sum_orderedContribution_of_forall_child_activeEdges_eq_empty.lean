-- Prove2me | solution 1 for BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_orderedContribution_of_forall_child_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:32:34.691045+00:00
-- url     : https://prove2.me/submissions/197e0569-a370-4786-b1ae-5701ca994929

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_sum_allBranchesBoundaryExpansion
import Theorems.Thm_BKAR_Forest_integral_allBranchesBoundaryExpansion_empty_singleton_eq_orderedContribution

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
        Finset.sum (Forest.empty V).activeEdges.attach
          (fun e =>
            (choices (Forest.empty V) e).forest.orderedContribution
              [e.val] ρ) := by
  rw [rho_oneConfig_eq_orderedSectorSum_empty_add_sum_allBranchesBoundaryExpansion
    choices ρ hanalytic]
  apply congrArg
    (fun r => (Forest.empty V).orderedSectorSum ρ + r)
  apply Finset.sum_congr rfl
  intro e _
  exact
    integral_allBranchesBoundaryExpansion_empty_singleton_eq_orderedContribution
      choices e ρ (hterm e)
end BKAR.Forest
