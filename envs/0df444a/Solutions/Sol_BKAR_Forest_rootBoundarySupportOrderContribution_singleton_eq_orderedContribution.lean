-- Prove2me | solution 1 for BKAR.Forest.rootBoundarySupportOrderContribution_singleton_eq_orderedContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:19:16.777732+00:00
-- url     : https://prove2.me/submissions/e019933f-4be9-4582-be6f-efef7ed9c5de

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_treeFiber_of_edges_ne_empty
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_empty_singleton_eq_localBoundary
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_ForestIndex_singleton_edges
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_activeExtension_forest_support_eq_singleton_empty
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_localBoundarySupportOrderContribution_def
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
    (a : Edge V) (ρ : (Edge V → ℝ) → ℝ) :
    rootBoundarySupportOrderContribution choices ρ (ForestIndex.singleton a) [a] =
      (choices (Forest.empty V) (emptyActiveEdge a)).forest.orderedContribution
        [a] ρ := by
  have hnonempty : (ForestIndex.singleton a : ForestIndex V).edges ≠ ∅ := by
    rw [ForestIndex.singleton_edges]
    exact Finset.singleton_ne_empty a
  rw [rootBoundarySupportOrderContribution_eq_treeFiber_of_edges_ne_empty
    choices ρ (ForestIndex.singleton a) [a] hnonempty]
  rw [boundarySupportOrderTreeFiber_empty_singleton_eq_localBoundary]
  rw [localBoundarySupportOrderContribution_def]
  have hfilter :
      (Forest.empty V).activeEdges.attach.filter
          (fun e =>
            (choices (Forest.empty V) e).forest.support =
                ForestIndex.singleton a ∧
              [] ++ [e.val] = [a]) =
        {emptyActiveEdge a} := by
    ext e
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      apply Subtype.ext
      have horder := h.2.2
      simp only [List.nil_append] at horder
      injection horder
    · intro h
      rw [h]
      constructor
      · exact Finset.mem_attach _ _
      · constructor
        · exact activeExtension_forest_support_eq_singleton_empty
            (choices (Forest.empty V) (emptyActiveEdge a))
        · simp
  rw [hfilter, Finset.sum_singleton]
  simp only [orderedContribution, orderedSimplexIntegral, emptyActiveEdge_val,
    List.nil_append]
end BKAR.Forest
