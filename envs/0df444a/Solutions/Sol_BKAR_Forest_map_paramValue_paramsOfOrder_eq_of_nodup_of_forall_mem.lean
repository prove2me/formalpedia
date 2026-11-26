-- Prove2me | solution 1 for BKAR.Forest.map_paramValue_paramsOfOrder_eq_of_nodup_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:30:21.246887+00:00
-- url     : https://prove2.me/submissions/d2201038-a893-4acc-b94d-93aa0b6247a4

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_paramsOfOrder_cons_of_ne
import Theorems.Thm_BKAR_Forest_paramsOfOrder_cons_self
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
    (F : Forest V) :
    ∀ (order : List (Edge V)) {ts : List ℝ},
      order.Nodup →
      (∀ e ∈ order, e ∈ F.edges) →
      ts.length = order.length →
      order.map (F.paramValue (F.paramsOfOrder order ts)) = ts
  | [], ts, _hnodup, _hmem, hlen => by
      have hts : ts = [] := List.length_eq_zero_iff.mp hlen
      rw [hts]
      rfl
  | e :: order, [], _hnodup, _hmem, hlen => by
      simp at hlen
  | e :: order, t :: ts, hnodup, hmem, hlen => by
      have he : e ∈ F.edges := hmem e (by simp)
      have hnotMem : e ∉ order := (List.nodup_cons.mp hnodup).1
      have htailNodup : order.Nodup := (List.nodup_cons.mp hnodup).2
      have htailMem : ∀ e' ∈ order, e' ∈ F.edges := by
        intro e' he'
        exact hmem e' (List.mem_cons_of_mem e he')
      have htailLen : ts.length = order.length := by
        simpa using hlen
      have htailMap :
          order.map (F.paramValue (F.paramsOfOrder (e :: order) (t :: ts))) =
            order.map (F.paramValue (F.paramsOfOrder order ts)) := by
        apply List.map_congr_left
        intro e' he'
        have he'F : e' ∈ F.edges := htailMem e' he'
        have hne : e' ≠ e := by
          intro h
          exact hnotMem (h ▸ he')
        rw [F.paramValue_of_mem _ he'F, F.paramValue_of_mem _ he'F]
        exact F.paramsOfOrder_cons_of_ne order t ts he'F hne
      rw [List.map_cons]
      rw [F.paramValue_of_mem _ he]
      rw [F.paramsOfOrder_cons_self e order t ts he]
      rw [htailMap]
      rw [solution
        F order htailNodup htailMem htailLen]
end BKAR.Forest
