-- Prove2me | solution 1 for BKAR.Forest.grownForestForSupportOrder_standardInterp_orderMeasurableEquiv_symm_eq_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:04:04.255514+00:00
-- url     : https://prove2.me/submissions/198f2430-6396-4715-9fdd-cb907c968ef7

import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Theorems.Thm_BKAR_ForestIndex_canonicalOrder_val
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_edges
import Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_order_mem_edgeOrders
import Theorems.Thm_BKAR_Forest_edgeParamFinEquivOfOrder_apply_val
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_edges
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_order_mem_edgeOrders
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_Forest_standardInterp_paramsOfOrder_eq_of_edges_eq
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
attribute [local simp] BKAR.Forest.edgeParamFinEquivOfOrder_apply_val
attribute [local simp] BKAR.Forest.emptyActiveEdge_val
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.ForestIndex.canonicalOrder_val
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
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ts : Fin order.val.length → ℝ) :
    (grownForestForSupportOrder choices I order).standardInterp
        ((Forest.orderMeasurableEquivOfOrder
            (grownForestForSupportOrder choices I order)
            (grownForestForSupportOrder_order_mem_edgeOrders
              choices I order)).symm ts) =
      (canonicalGrownForestForSupport choices I).standardInterp
        ((Forest.orderMeasurableEquivOfOrder
            (canonicalGrownForestForSupport choices I)
            (canonicalGrownForestForSupport_order_mem_edgeOrders
              choices I order.property)).symm ts) := by
  let F : Forest V := grownForestForSupportOrder choices I order
  let G : Forest V := canonicalGrownForestForSupport choices I
  have hForder : order.val ∈ F.edgeOrders := by
    simpa [F] using grownForestForSupportOrder_order_mem_edgeOrders choices I order
  have hGorder : order.val ∈ G.edgeOrders := by
    simpa [G] using
      canonicalGrownForestForSupport_order_mem_edgeOrders
        choices I order.property
  have hedges : F.edges = G.edges := by
    simp [F, G, grownForestForSupportOrder_edges,
      canonicalGrownForestForSupport_edges]
  change
    F.standardInterp
        ((F.orderMeasurableEquivOfOrder hForder).symm ts) =
      G.standardInterp
        ((G.orderMeasurableEquivOfOrder hGorder).symm ts)
  rw [← F.paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm hForder ts]
  rw [← G.paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm hGorder ts]
  exact F.standardInterp_paramsOfOrder_eq_of_edges_eq G hedges
    order.val (List.ofFn ts)
end BKAR.Forest
