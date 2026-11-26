-- Prove2me | solution 1 for BKAR.Forest.cons_mem_edgeSetOrders_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:49:06.34+00:00
-- url     : https://prove2.me/submissions/4e29f547-6777-41a8-acc7-7b2357daa44e

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_mem_edgeSetOrders_iff_toFinset_eq_and_nodup
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
omit [Fintype V]
namespace BKAR.Forest
theorem _root_.solution
    (S : Finset (Edge V)) {e : Edge V} {order : List (Edge V)} :
    e :: order ∈ edgeSetOrders S ↔
      e ∈ S ∧ order ∈ edgeSetOrders (S.erase e) := by
  rw [mem_edgeSetOrders_iff_toFinset_eq_and_nodup]
  rw [mem_edgeSetOrders_iff_toFinset_eq_and_nodup]
  constructor
  · intro h
    rw [List.toFinset_cons] at h
    rw [List.nodup_cons] at h
    rcases h with ⟨hset, hnotMem, hnodup⟩
    have heS : e ∈ S := by
      rw [← hset]
      exact Finset.mem_insert_self e order.toFinset
    refine ⟨heS, ?_⟩
    constructor
    · ext x
      by_cases hxe : x = e
      · subst x
        rw [Finset.mem_erase, List.mem_toFinset]
        constructor
        · intro hx
          exact False.elim (hnotMem hx)
        · intro hx
          exact False.elim (hx.1 rfl)
      · rw [Finset.mem_erase, List.mem_toFinset]
        constructor
        · intro hx
          exact ⟨hxe, by
            rw [← hset]
            exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr hx)⟩
        · intro hx
          have hxS : x ∈ insert e order.toFinset := by
            rw [hset]
            exact hx.2
          rw [Finset.mem_insert] at hxS
          exact hxS.elim (fun h => False.elim (hxe h))
            (fun hxFin => List.mem_toFinset.mp hxFin)
    · exact hnodup
  · intro h
    rcases h with ⟨heS, htail⟩
    rcases htail with ⟨hset, hnodup⟩
    rw [List.toFinset_cons]
    rw [List.nodup_cons]
    constructor
    · ext x
      rw [Finset.mem_insert]
      by_cases hxe : x = e
      · subst x
        simp [heS]
      · rw [hset, Finset.mem_erase]
        constructor
        · intro hx
          exact hx.elim (fun h => False.elim (hxe h)) (fun h => h.2)
        · intro hx
          exact Or.inr ⟨hxe, hx⟩
    · constructor
      · intro heOrder
        have heErase : e ∈ S.erase e := by
          rw [← hset, List.mem_toFinset]
          exact heOrder
        exact (Finset.notMem_erase e S) heErase
      · exact hnodup
end BKAR.Forest
