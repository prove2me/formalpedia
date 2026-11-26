-- Prove2me | solution 1 for BKAR.Forest.paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:32:41.865797+00:00
-- url     : https://prove2.me/submissions/e754a498-17d8-41f6-90f0-63b0136d72e7

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Theorems.Thm_BKAR_Forest_edgeParamFinEquivOfOrder_apply_val
import Theorems.Thm_BKAR_Forest_orderMeasurableEquivOfOrder_apply
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_map_paramValue_paramsOfOrder_eq_of_mem_edgeOrders
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
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ts : Fin order.length → ℝ) :
    F.paramsOfOrder order (List.ofFn ts) =
      (F.orderMeasurableEquivOfOrder horder).symm ts := by
  apply (F.orderMeasurableEquivOfOrder horder).injective
  funext i
  have hmap :
      order.map (F.paramValue (F.paramsOfOrder order (List.ofFn ts))) =
        List.ofFn ts := by
    exact F.map_paramValue_paramsOfOrder_eq_of_mem_edgeOrders horder (by simp)
  have hget := congrArg (fun xs : List ℝ => xs[i.val]?) hmap
  have hcoord :
      F.paramValue (F.paramsOfOrder order (List.ofFn ts)) (order.get i) =
        ts i := by
    have hsome :
        some (F.paramValue (F.paramsOfOrder order (List.ofFn ts)) (order.get i)) =
          some (ts i) := by
      simpa [List.getElem?_map, List.getElem?_ofFn, i.isLt] using hget
    exact Option.some.inj hsome
  calc
    F.orderMeasurableEquivOfOrder horder
        (F.paramsOfOrder order (List.ofFn ts)) i
        = F.paramValue (F.paramsOfOrder order (List.ofFn ts)) (order.get i) := by
          rw [F.orderMeasurableEquivOfOrder_apply horder]
    _ = ts i := hcoord
    _ = F.orderMeasurableEquivOfOrder horder
        ((F.orderMeasurableEquivOfOrder horder).symm ts) i := by
          exact congrFun
            ((F.orderMeasurableEquivOfOrder horder).apply_symm_apply ts).symm i
end BKAR.Forest
