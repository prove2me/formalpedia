-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.params_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:37:53.774638+00:00
-- url     : https://prove2.me/submissions/9368a0bc-6250-4319-9543-84804cfa3617

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_initial
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_new
import Theorems.Thm_BKAR_Forest_EdgeExtension_new_mem
import Theorems.Thm_BKAR_Forest_OrderedGrowth_initial_edges_subset_edges
import Theorems.Thm_BKAR_Forest_OrderedGrowth_mem_edges_of_mem_order
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


attribute [local simp] BKAR.Forest.OrderedGrowth.params_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_cons

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F (e :: order) G)
    (u : F.EdgeParam → ℝ) (t : ℝ) (ts : List ℝ) :
    h.params u (t :: ts) ⟨e, h.mem_edges_of_mem_order
      (by rw [List.mem_cons]; exact Or.inl rfl)⟩ = t := by
  cases h with
  | cons step tail =>
      rw [params_cons_cons]
      rw [show ⟨e, (OrderedGrowth.cons step tail).mem_edges_of_mem_order
          (by rw [List.mem_cons]; exact Or.inl rfl)⟩ =
          ⟨e, tail.initial_edges_subset_edges step.new_mem⟩
          from Subtype.ext rfl]
      rw [tail.params_initial (step.extendParam u t) ts ⟨e, step.new_mem⟩]
      rw [step.extendParam_new u t]
end BKAR.Forest.OrderedGrowth
