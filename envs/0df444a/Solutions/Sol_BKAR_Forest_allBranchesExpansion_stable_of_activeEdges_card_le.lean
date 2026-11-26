-- Prove2me | solution 1 for BKAR.Forest.allBranchesExpansion_stable_of_activeEdges_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:38.751799+00:00
-- url     : https://prove2.me/submissions/9a3770f7-7cb8-4017-ac0e-2b4ee63daf0c

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_allBranchesExpansion_zero
import Theorems.Thm_BKAR_Forest_allBranchesExpansion_succ
import Theorems.Thm_BKAR_Forest_allBranchesExpansion_succ_of_activeEdges_eq_empty
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_ActiveExtension_activeEdges_card_lt
import Theorems.Thm_BKAR_Forest_EdgeExtension_activeEdges_card_lt
import Theorems.Thm_BKAR_Forest_mixedPartialList_interpWithFill_eq_standardInterp_of_activeEdges_eq_empty


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      allBranchesExpansion choices (n + 1) F pref prefixTs top ρ =
        allBranchesExpansion choices n F pref prefixTs top ρ
  | 0, F, pref, prefixTs, top, ρ, hle => by
      have hcard : F.activeEdges.card = 0 :=
        Nat.eq_zero_of_le_zero hle
      have hF : F.activeEdges = ∅ :=
        Finset.card_eq_zero.mp hcard
      rw [allBranchesExpansion_succ_of_activeEdges_eq_empty choices 0 F
        pref prefixTs top ρ hF]
      rw [allBranchesExpansion_zero]
      rw [F.mixedPartialList_interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
        pref.reverse (F.paramsOfOrder pref prefixTs) ρ top hF]
  | n + 1, F, pref, prefixTs, top, ρ, hle => by
      rw [allBranchesExpansion_succ, allBranchesExpansion_succ]
      apply congrArg
        (fun r =>
          mixedPartialList pref.reverse ρ
            (F.standardInterp (F.paramsOfOrder pref prefixTs)) + r)
      apply Finset.sum_congr rfl
      intro e _
      apply intervalIntegral.integral_congr
      intro t _
      have hlt :
          (choices F e).forest.activeEdges.card < F.activeEdges.card :=
        (choices F e).activeEdges_card_lt
      have hchild_le : (choices F e).forest.activeEdges.card ≤ n :=
        Nat.lt_succ_iff.mp (hlt.trans_le hle)
      exact
        solution choices n
          (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ
          hchild_le
end BKAR.Forest
