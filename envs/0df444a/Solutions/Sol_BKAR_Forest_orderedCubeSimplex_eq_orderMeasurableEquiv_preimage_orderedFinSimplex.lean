-- Prove2me | solution 1 for BKAR.Forest.orderedCubeSimplex_eq_orderMeasurableEquiv_preimage_orderedFinSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:37:24.496718+00:00
-- url     : https://prove2.me/submissions/360f53ab-bd80-49a2-b6db-9436f2953936

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Theorems.Thm_BKAR_Forest_edgeParamFinEquivOfOrder_apply_val
import Theorems.Thm_BKAR_Forest_orderMeasurableEquivOfOrder_apply_edgeParam
import Theorems.Thm_BKAR_Forest_orderMeasurableEquivOfOrder_apply
import Theorems.Thm_BKAR_Forest_mem_orderedFinSimplex_iff
import Theorems.Thm_BKAR_Forest_map_paramValue_eq_ofFn_orderMeasurableEquiv
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_mem_orderedCubeSimplex_iff
import Theorems.Thm_BKAR_Forest_mem_unitCube_iff
import Theorems.Thm_BKAR_Forest_paramValue_mem_Icc
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


attribute [local simp] BKAR.Forest.edgeParamFinEquivOfOrder_apply_val

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders) :
    F.orderedCubeSimplex order =
      (F.orderMeasurableEquivOfOrder horder) ⁻¹'
        orderedFinSimplex order.length := by
  ext u
  rw [mem_orderedCubeSimplex_iff]
  change
    u ∈ F.unitCube ∧ OrderedSimplexParams 1 (order.map (F.paramValue u)) ↔
      F.orderMeasurableEquivOfOrder horder u ∈ orderedFinSimplex order.length
  rw [mem_orderedFinSimplex_iff]
  constructor
  · intro h
    constructor
    · intro i
      have hcube := (F.mem_unitCube_iff u).mp h.1
      have hbounds := F.paramValue_mem_Icc u hcube (order.get i)
      simpa [F.orderMeasurableEquivOfOrder_apply horder u i] using hbounds
    · rw [← F.map_paramValue_eq_ofFn_orderMeasurableEquiv horder u]
      exact h.2
  · intro h
    constructor
    · rw [F.mem_unitCube_iff]
      intro p
      let i : Fin order.length := (F.edgeParamFinEquivOfOrder horder).symm p
      have hp : F.edgeParamFinEquivOfOrder horder i = p := by
        dsimp [i]
        exact (F.edgeParamFinEquivOfOrder horder).apply_symm_apply p
      have hread :
          F.orderMeasurableEquivOfOrder horder u i =
            u (F.edgeParamFinEquivOfOrder horder i) :=
        F.orderMeasurableEquivOfOrder_apply_edgeParam horder u i
      have hbounds := h.1 i
      rw [hp] at hread
      simpa [hread] using hbounds
    · rw [F.map_paramValue_eq_ofFn_orderMeasurableEquiv horder u]
      exact h.2
end BKAR.Forest
