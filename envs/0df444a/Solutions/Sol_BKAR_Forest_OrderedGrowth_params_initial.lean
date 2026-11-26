-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.params_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:32:02.76363+00:00
-- url     : https://prove2.me/submissions/ef7b04da-8387-4699-b24b-65ca7ed0d879

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_old
import Theorems.Thm_BKAR_Forest_EdgeExtension_old_mem
import Theorems.Thm_BKAR_Forest_OrderedGrowth_initial_edges_subset_edges
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
theorem _root_.solution (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ) (e : F.EdgeParam) :
    h.params u ts ⟨e.val, h.initial_edges_subset_edges e.property⟩ = u e := by
  induction h generalizing ts with
  | nil F =>
      rw [show (⟨e.val, (OrderedGrowth.nil F).initial_edges_subset_edges
          e.property⟩ : F.EdgeParam) = e from Subtype.ext rfl]
      rfl
  | cons step tail ih =>
      cases ts with
      | nil =>
          rw [params_cons_nil]
          rw [show ⟨e.val, (OrderedGrowth.cons step tail).initial_edges_subset_edges
              e.property⟩ =
              ⟨e.val, tail.initial_edges_subset_edges (step.old_mem e.property)⟩
              from Subtype.ext rfl]
          rw [ih (step.extendParam u 0) []
            ⟨e.val, step.old_mem e.property⟩]
          rw [step.extendParam_old u 0 e.property]
      | cons t ts =>
          rw [params_cons_cons]
          rw [show ⟨e.val, (OrderedGrowth.cons step tail).initial_edges_subset_edges
              e.property⟩ =
              ⟨e.val, tail.initial_edges_subset_edges (step.old_mem e.property)⟩
              from Subtype.ext rfl]
          rw [ih (step.extendParam u t) ts
            ⟨e.val, step.old_mem e.property⟩]
          rw [step.extendParam_old u t e.property]
end BKAR.Forest.OrderedGrowth
