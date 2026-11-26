-- Prove2me | solution 1 for BKAR.Forest.rho_oneConfig_eq_allBranchesBoundaryExpansion_empty_activeEdges_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:45:29.063836+00:00
-- url     : https://prove2.me/submissions/4bf31ba1-7682-41b0-8619-010418e785e2

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_allBranchesExpansion_activeEdges_card_eq_boundaryExpansion
import Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_allBranchesExpansion_empty

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
      allBranchesBoundaryExpansion choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ := by
  rw [← allBranchesExpansion_activeEdges_card_eq_boundaryExpansion
    choices (Forest.empty V) [] [] 1 ρ]
  exact rho_oneConfig_eq_allBranchesExpansion_empty choices
    (Forest.empty V).activeEdges.card ρ hanalytic
end BKAR.Forest
