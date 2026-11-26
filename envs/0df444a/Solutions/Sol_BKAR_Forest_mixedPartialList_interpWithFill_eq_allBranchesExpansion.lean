-- Prove2me | solution 1 for BKAR.Forest.mixedPartialList_interpWithFill_eq_allBranchesExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:13:39.384803+00:00
-- url     : https://prove2.me/submissions/ca07bc2c-8e4d-45a5-899c-a785a7e5c93f

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_allBranchesExpansion_zero
import Theorems.Thm_BKAR_Forest_allBranchesExpansion_succ
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_eq_paramsOfOrder_append_singleton
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_mixedPartialList_interpWithFill_eq_standardInterp_add_sum_activeExtensions
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
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      pref.toFinset = F.edges →
      prefixTs.length = pref.length →
      allBranchesAnalytic choices n F pref prefixTs top ρ →
      mixedPartialList pref.reverse ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) top) =
        allBranchesExpansion choices n F pref prefixTs top ρ
  | 0, F, pref, prefixTs, top, ρ, _hpref, _hprefixTs, _hanalytic => by
      rw [allBranchesExpansion_zero]
  | n + 1, F, pref, prefixTs, top, ρ, hpref, hprefixTs, hanalytic => by
      rcases hanalytic with ⟨hbound, hρ, hint, _hstd, _hrec, hchild⟩
      have hstep :=
        F.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_activeExtensions
          pref.reverse (F.paramsOfOrder pref prefixTs) ρ top
          hbound hρ hint (choices F)
      calc
        mixedPartialList pref.reverse ρ
            (F.interpWithFill (F.paramsOfOrder pref prefixTs) top) =
          mixedPartialList pref.reverse ρ
              (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
            Finset.sum F.activeEdges.attach
              (fun e => ∫ t in 0..top,
                mixedPartialList (e.val :: pref.reverse) ρ
                  ((choices F e).forest.interpWithFill
                    ((choices F e).extension.extendParam
                      (F.paramsOfOrder pref prefixTs) t) t)) := by
            exact hstep
        _ =
          mixedPartialList pref.reverse ρ
              (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
            Finset.sum F.activeEdges.attach
              (fun e => ∫ t in 0..top,
                allBranchesExpansion choices n (choices F e).forest
                  (pref ++ [e.val]) (prefixTs ++ [t]) t ρ) := by
            apply congrArg
              (fun r =>
                mixedPartialList pref.reverse ρ
                    (F.standardInterp (F.paramsOfOrder pref prefixTs)) + r)
            apply Finset.sum_congr rfl
            intro e _
            apply intervalIntegral.integral_congr
            intro t ht
            have hprefChild :
                (pref ++ [e.val]).toFinset = (choices F e).forest.edges := by
              rw [List.toFinset_append, (choices F e).extension.edges_eq,
                hpref]
              simp
            have hprefixTsChild :
                (prefixTs ++ [t]).length = (pref ++ [e.val]).length := by
              simp [hprefixTs]
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
            change mixedPartialList (e.val :: pref.reverse) ρ
                ((choices F e).forest.interpWithFill
                  ((choices F e).extension.extendParam
                    (F.paramsOfOrder pref prefixTs) t) t) =
              allBranchesExpansion choices n (choices F e).forest
                (pref ++ [e.val]) (prefixTs ++ [t]) t ρ
            rw [← horder, hparam]
            exact
              solution
                choices n (choices F e).forest (pref ++ [e.val])
                (prefixTs ++ [t]) t ρ hprefChild hprefixTsChild
                (hchild e t ht)
        _ =
          allBranchesExpansion choices (n + 1) F pref prefixTs top ρ := by
            rw [allBranchesExpansion_succ]
end BKAR.Forest
