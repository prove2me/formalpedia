-- Prove2me | solution 1 for BKAR.Forest.allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:46:48.673391+00:00
-- url     : https://prove2.me/submissions/2955adc8-0c02-4a79-a463-e20f6178ae91

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_zero
import Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_succ
import Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_eq_activeEdges_card_of_card_le
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_ActiveExtension_activeEdges_card_lt
import Theorems.Thm_BKAR_Forest_EdgeExtension_activeEdges_card_lt


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
    allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            allBranchesBoundaryExpansion choices
              (choices F e).forest.activeEdges.card
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t ρ) := by
  by_cases hF : F.activeEdges = ∅
  · have hcard : F.activeEdges.card = 0 := by
      rw [hF, Finset.card_empty]
    rw [hcard, allBranchesBoundaryExpansion_zero]
    have hattach : F.activeEdges.attach = ∅ := by
      rw [hF]
      rfl
    rw [hattach, Finset.sum_empty, add_zero]
  · have hcard_pos : 0 < F.activeEdges.card := by
      exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hF)
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard_pos) with
      ⟨n, hn⟩
    rw [hn, allBranchesBoundaryExpansion_succ]
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
    have hchild_le : (choices F e).forest.activeEdges.card ≤ n := by
      rw [hn] at hlt
      exact Nat.lt_succ_iff.mp hlt
    exact
      allBranchesBoundaryExpansion_eq_activeEdges_card_of_card_le
        choices n (choices F e).forest (pref ++ [e.val])
        (prefixTs ++ [t]) t ρ hchild_le
end BKAR.Forest
