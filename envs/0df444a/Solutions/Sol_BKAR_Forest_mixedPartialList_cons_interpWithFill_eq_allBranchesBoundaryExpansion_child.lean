-- Prove2me | solution 1 for BKAR.Forest.mixedPartialList_cons_interpWithFill_eq_allBranchesBoundaryExpansion_child
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:46:53.177908+00:00
-- url     : https://prove2.me/submissions/67b28e05-563a-43a2-b5f7-e8b5e490655b

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_allBranchesAnalytic_of_le
import Theorems.Thm_BKAR_Forest_mixedPartialList_interpWithFill_eq_allBranchesBoundaryExpansion_activeEdges_card
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_ActiveExtension_activeEdges_card_lt
import Theorems.Thm_BKAR_Forest_EdgeExtension_activeEdges_card_lt
import Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_eq_paramsOfOrder_append_singleton
import Theorems.Thm_BKAR_Forest_EdgeExtension_mixedPartialList_cons_interpWithFill_eq_extension
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_edgeBasis_self
import Theorems.Thm_BKAR_mixedPartialList_cons
import Theorems.Thm_BKAR_mixedPartialList_cons_apply
import Theorems.Thm_BKAR_mixedPartialList_nil
import Theorems.Thm_BKAR_mixedPartialList_nil_apply
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_cons
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_nil
import Theorems.Thm_BKAR_orderedSimplexIntegral_cons
import Theorems.Thm_BKAR_orderedSimplexIntegral_nil
import Theorems.Thm_BKAR_orderedSimplexParams_cons
import Theorems.Thm_BKAR_orderedSimplexParams_nil
import Theorems.Thm_BKAR_updateCoord_same_value
import Theorems.Thm_BKAR_updateCoord_self
import Theorems.Thm_BKAR_updateCoord_update_same
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegralAux_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegral_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegrand_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.derivativeOrder_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_cons
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_nil
attribute [local simp] BKAR.Forest.emptyActiveEdge_val
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.edgeBasis_self
attribute [local simp] BKAR.mixedPartialList_cons
attribute [local simp] BKAR.mixedPartialList_cons_apply
attribute [local simp] BKAR.mixedPartialList_nil
attribute [local simp] BKAR.mixedPartialList_nil_apply
attribute [local simp] BKAR.orderedSimplexIntegralAux_cons
attribute [local simp] BKAR.orderedSimplexIntegralAux_nil
attribute [local simp] BKAR.orderedSimplexIntegral_cons
attribute [local simp] BKAR.orderedSimplexIntegral_nil
attribute [local simp] BKAR.orderedSimplexParams_cons
attribute [local simp] BKAR.orderedSimplexParams_nil
attribute [local simp] BKAR.updateCoord_same_value
attribute [local simp] BKAR.updateCoord_self
attribute [local simp] BKAR.updateCoord_update_same



set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ)
    {t : ℝ} (ht : t ∈ Set.uIcc 0 top) :
    mixedPartialList (e.val :: pref.reverse) ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) t) =
      allBranchesBoundaryExpansion choices
        (choices F e).forest.activeEdges.card
        (choices F e).forest (pref ++ [e.val])
        (prefixTs ++ [t]) t ρ := by
  have hcard_pos : 0 < F.activeEdges.card :=
    Finset.card_pos.mpr ⟨e.val, e.property⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard_pos) with
    ⟨n, hn⟩
  rw [hn] at hanalytic
  rcases hanalytic with ⟨hbound, _hρ, _hint, _hstd, _hrec, hchild⟩
  have horder :
      (pref ++ [e.val]).reverse = e.val :: pref.reverse := by
    rw [List.reverse_append]
    rfl
  have hparam :
      (choices F e).extension.extendParam
          (F.paramsOfOrder pref prefixTs) t =
        (choices F e).forest.paramsOfOrder (pref ++ [e.val])
          (prefixTs ++ [t]) :=
    (choices F e).extension.extendParam_eq_paramsOfOrder_append_singleton
      pref prefixTs t hpref hprefixTs
  have hprefChild :
      (pref ++ [e.val]).toFinset = (choices F e).forest.edges := by
    rw [List.toFinset_append, (choices F e).extension.edges_eq,
      hpref]
    simp
  have hprefixTsChild :
      (prefixTs ++ [t]).length = (pref ++ [e.val]).length := by
    simp [hprefixTs]
  have hchild_le :
      (choices F e).forest.activeEdges.card ≤ n := by
    have hlt :
        (choices F e).forest.activeEdges.card < F.activeEdges.card :=
      (choices F e).activeEdges_card_lt
    rw [hn] at hlt
    exact Nat.lt_succ_iff.mp hlt
  have hchildExactAnalytic :
      allBranchesAnalytic choices
        (choices F e).forest.activeEdges.card
        (choices F e).forest (pref ++ [e.val])
        (prefixTs ++ [t]) t ρ :=
    allBranchesAnalytic_of_le choices hchild_le (hchild e t ht)
  calc
    mixedPartialList (e.val :: pref.reverse) ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) t) =
      partialDeriv e.val (mixedPartialList pref.reverse ρ)
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) t) := by
        rw [mixedPartialList_cons_apply]
    _ =
      mixedPartialList (e.val :: pref.reverse) ρ
        ((choices F e).forest.interpWithFill
          ((choices F e).extension.extendParam
            (F.paramsOfOrder pref prefixTs) t) t) := by
        exact
          EdgeExtension.mixedPartialList_cons_interpWithFill_eq_extension
            ((choices F e).extension) pref.reverse
            (F.paramsOfOrder pref prefixTs) ρ
            (hbound t ht)
    _ =
      mixedPartialList (pref ++ [e.val]).reverse ρ
        ((choices F e).forest.interpWithFill
          ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
            (prefixTs ++ [t])) t) := by
        rw [horder, ← hparam]
    _ =
      allBranchesBoundaryExpansion choices
        (choices F e).forest.activeEdges.card
        (choices F e).forest (pref ++ [e.val])
        (prefixTs ++ [t]) t ρ := by
        exact
          mixedPartialList_interpWithFill_eq_allBranchesBoundaryExpansion_activeEdges_card
            choices (choices F e).forest (pref ++ [e.val])
            (prefixTs ++ [t]) t ρ hprefChild hprefixTsChild
            hchildExactAnalytic
end BKAR.Forest
