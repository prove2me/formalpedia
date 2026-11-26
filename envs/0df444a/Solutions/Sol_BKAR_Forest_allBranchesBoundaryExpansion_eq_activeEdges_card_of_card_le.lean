-- Prove2me | solution 1 for BKAR.Forest.allBranchesBoundaryExpansion_eq_activeEdges_card_of_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:45:48.199413+00:00
-- url     : https://prove2.me/submissions/ad69b599-1daf-481b-b16e-a87773f88915

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_activeEdges_card_add

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (n : Nat) (F : Forest V) (pref : List (Edge V))
    (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hle : F.activeEdges.card ≤ n) :
    allBranchesBoundaryExpansion choices n F pref prefixTs top ρ =
      allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ := by
  rcases exists_add_of_le hle with ⟨k, rfl⟩
  exact allBranchesBoundaryExpansion_activeEdges_card_add
    choices k F pref prefixTs top ρ
end BKAR.Forest
