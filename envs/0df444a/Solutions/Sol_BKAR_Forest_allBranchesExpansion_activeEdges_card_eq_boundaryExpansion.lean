-- Prove2me | solution 1 for BKAR.Forest.allBranchesExpansion_activeEdges_card_eq_boundaryExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:16.689413+00:00
-- url     : https://prove2.me/submissions/742a2607-be11-4057-9933-fefcfcaa3c10

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_allBranchesExpansion_eq_boundaryExpansion_of_activeEdges_card_le

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    allBranchesExpansion choices F.activeEdges.card F pref prefixTs top ρ =
      allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ :=
  allBranchesExpansion_eq_boundaryExpansion_of_activeEdges_card_le
    choices F.activeEdges.card F pref prefixTs top ρ le_rfl
end BKAR.Forest
