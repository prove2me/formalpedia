-- Prove2me | solution 1 for BKAR.Forest.rootBoundarySupportOrderContribution_pair_eq_orderedContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:40.673072+00:00
-- url     : https://prove2.me/submissions/122d1c7f-798d-42be-a0fc-82642debddac

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_integral_child_of_tail_ne_nil
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_localBoundary_of_order_length_eq_succ
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_localBoundarySupportOrderContribution_def
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_treeFiber_of_not_empty_marker
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
    (a b : Edge V) (ρ : (Edge V → ℝ) → ℝ)
    (hb :
      b ∈ (choices (Forest.empty V) (emptyActiveEdge a)).forest.activeEdges) :
    rootBoundarySupportOrderContribution choices ρ
        ((choices (choices (Forest.empty V) (emptyActiveEdge a)).forest
          ⟨b, hb⟩).forest.support) [a, b] =
      (choices (choices (Forest.empty V) (emptyActiveEdge a)).forest
        ⟨b, hb⟩).forest.orderedContribution [a, b] ρ := by
  let F₁ : Forest V :=
    (choices (Forest.empty V) (emptyActiveEdge a)).forest
  let e₂ : {e // e ∈ F₁.activeEdges} := ⟨b, hb⟩
  let F₂ : Forest V := (choices F₁ e₂).forest
  change
    rootBoundarySupportOrderContribution choices ρ F₂.support [a, b] =
      F₂.orderedContribution [a, b] ρ
  rw [rootBoundarySupportOrderContribution_eq_treeFiber_of_not_empty_marker
    choices ρ F₂.support [a, b] (by
      intro hmarker
      cases hmarker.2)]
  have heqEmpty :
      (⟨a, (emptyActiveEdge a).property⟩ :
        {e // e ∈ (Forest.empty V).activeEdges}) =
        emptyActiveEdge a := by
    apply Subtype.ext
    rfl
  rw [show
      boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
          F₂.support [a, b] ρ =
        ∫ t in 0..(1 : ℝ),
          boundarySupportOrderTreeFiber choices
            (choices (Forest.empty V)
              ⟨a, (emptyActiveEdge a).property⟩).forest
            ([] ++ [a]) ([] ++ [t]) t F₂.support [a, b] ρ by
    exact
      boundarySupportOrderTreeFiber_eq_integral_child_of_tail_ne_nil
        choices (Forest.empty V) [] [] 1 F₂.support a [b] ρ
        (emptyActiveEdge a).property (by simp)]
  rw [heqEmpty]
  rw [orderedContribution, orderedSimplexIntegral]
  apply intervalIntegral.integral_congr
  intro t _ht
  change
    boundarySupportOrderTreeFiber choices
        (choices (Forest.empty V) (emptyActiveEdge a)).forest
        ([] ++ [a]) ([] ++ [t]) t F₂.support [a, b] ρ = _
  rw [show
      boundarySupportOrderTreeFiber choices
          (choices (Forest.empty V) (emptyActiveEdge a)).forest
          ([] ++ [a]) ([] ++ [t]) t F₂.support [a, b] ρ =
        localBoundarySupportOrderContribution choices F₁ [a] [t] t
          F₂.support [a, b] ρ by
    change boundarySupportOrderTreeFiber choices F₁ [a] [t] t F₂.support
        [a, b] ρ =
      localBoundarySupportOrderContribution choices F₁ [a] [t] t
        F₂.support [a, b] ρ
    exact
      boundarySupportOrderTreeFiber_eq_localBoundary_of_order_length_eq_succ
        choices F₁ [a] [t] t F₂.support [a, b] ρ (by simp)]
  rw [localBoundarySupportOrderContribution_def]
  have hfilter :
      F₁.activeEdges.attach.filter
          (fun e =>
            (choices F₁ e).forest.support = F₂.support ∧
              [a] ++ [e.val] = [a, b]) =
        {e₂} := by
    ext e
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      exact Subtype.ext (by
        have horder := h.2.2
        have htail : [e.val] = [b] := (List.cons.inj horder).2
        exact (List.cons.inj htail).1)
    · intro h
      rw [h]
      constructor
      · exact Finset.mem_attach _ _
      · constructor
        · rfl
        · simp [e₂]
  rw [hfilter, Finset.sum_singleton]
  simp only [e₂, F₂, List.singleton_append]
end BKAR.Forest
