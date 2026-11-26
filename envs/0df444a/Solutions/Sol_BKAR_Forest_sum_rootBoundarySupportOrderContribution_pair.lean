-- Prove2me | solution 1 for BKAR.Forest.sum_rootBoundarySupportOrderContribution_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:34:56.5478+00:00
-- url     : https://prove2.me/submissions/adfe7001-bf9a-45af-8106-c578cc12b5b6

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_pair_eq_orderedContribution
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_empty_edges
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_zero_of_order_toFinset_ne_edges
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
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => rootBoundarySupportOrderContribution choices ρ I [a, b]) =
      (choices (choices (Forest.empty V) (emptyActiveEdge a)).forest
        ⟨b, hb⟩).forest.orderedContribution [a, b] ρ := by
  classical
  let F₁ : Forest V :=
    (choices (Forest.empty V) (emptyActiveEdge a)).forest
  let e₂ : {e // e ∈ F₁.activeEdges} := ⟨b, hb⟩
  let F₂ : Forest V := (choices F₁ e₂).forest
  have hF₁edges : F₁.edges = ({a} : Finset (Edge V)) := by
    change (choices (Forest.empty V) (emptyActiveEdge a)).forest.edges =
      ({a} : Finset (Edge V))
    rw [(choices (Forest.empty V) (emptyActiveEdge a)).extension.edges_eq,
      Forest.empty_edges]
    rfl
  have hF₂edges : [a, b].toFinset = F₂.support.edges := by
    change [a, b].toFinset = F₂.edges
    rw [show F₂.edges = insert b F₁.edges by
      exact (choices F₁ e₂).extension.edges_eq]
    rw [hF₁edges]
    ext x
    simp [or_comm]
  rw [Finset.sum_eq_single_of_mem F₂.support (Finset.mem_univ F₂.support)]
  · change
      rootBoundarySupportOrderContribution choices ρ
          ((choices (choices (Forest.empty V) (emptyActiveEdge a)).forest
            ⟨b, hb⟩).forest.support) [a, b] =
        (choices (choices (Forest.empty V) (emptyActiveEdge a)).forest
          ⟨b, hb⟩).forest.orderedContribution [a, b] ρ
    exact rootBoundarySupportOrderContribution_pair_eq_orderedContribution
      choices a b ρ hb
  · intro I _ hne
    exact
      rootBoundarySupportOrderContribution_eq_zero_of_order_toFinset_ne_edges
        choices ρ I [a, b] (by
          intro hI
          apply hne
          apply ForestIndex.ext
          rw [← hI, hF₂edges])
end BKAR.Forest
