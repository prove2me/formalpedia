-- Prove2me | solution 1 for BKAR.Forest.allBranchesExpansion_succ_of_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:42:44.464203+00:00
-- url     : https://prove2.me/submissions/7e85cf36-4d94-4d1c-b19b-d1182b390186

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_allBranchesExpansion_succ
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V) (n : Nat)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hF : F.activeEdges = ∅) :
    allBranchesExpansion choices (n + 1) F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) := by
  rw [allBranchesExpansion_succ]
  have hattach : F.activeEdges.attach = ∅ := by
    rw [hF]
    rfl
  rw [hattach, Finset.sum_empty, add_zero]
end BKAR.Forest
