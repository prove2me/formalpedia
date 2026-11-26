-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.supportContribution_eq_sum_support_edges_filter_tail_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:32:11.409069+00:00
-- url     : https://prove2.me/submissions/f9879379-c333-4d7d-bf26-b2675f439e29

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_eq_sum_first_mem_and_tail_order
import Theorems.Thm_BKAR_ForestIndex_ext
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
import Theorems.Thm_BKAR_OrderedSimplexParams_tail
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
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveTerminalBranchData
theorem _root_.solution
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ =
      Finset.sum
        (I.edges.attach.filter
          (fun e =>
            (data.tail (emptyActiveEdge e.val)).order ∈
              edgeSetOrders (I.edges.erase e.val)))
        (fun e => (data.growth (emptyActiveEdge e.val)).terminal.orderedContribution
          (data.growthOrder (emptyActiveEdge e.val)) ρ) := by
  rw [data.supportContribution_eq_sum_first_mem_and_tail_order I ρ]
  refine Finset.sum_bij
    (fun e he =>
      ⟨e.val, (Finset.mem_filter.mp he).2.1⟩)
    ?hmem ?hinj ?hsurj ?hterm
  · intro e he
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_attach _ _, by
      have htail := (Finset.mem_filter.mp he).2.2
      simpa only [emptyActiveEdge_val] using! htail⟩
  · intro e₁ _ e₂ _ heq
    apply Subtype.ext
    exact congrArg
      (fun x : {x : Edge V // x ∈ I.edges} => (x : Edge V)) heq
  · intro e he
    rw [Finset.mem_filter] at he
    refine ⟨emptyActiveEdge e.val, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_attach _ _, by
        constructor
        · simpa only [emptyActiveEdge_val] using e.property
        · simpa only [emptyActiveEdge_val] using he.2⟩
    · apply Subtype.ext
      rw [emptyActiveEdge_val]
  · intro e _
    have heq : e = emptyActiveEdge e.val := by
      apply Subtype.ext
      rw [emptyActiveEdge_val]
    cases heq
    rfl
end BKAR.Forest.ActiveTerminalBranchData
