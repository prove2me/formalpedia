-- Prove2me | solution 1 for BKAR.Forest.paramsOfOrder_eq_orderMeasurableEquiv_symm_getD_of_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:39.724302+00:00
-- url     : https://prove2.me/submissions/02b254d3-59da-42b2-801e-5a89cdd5652c

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_Forest_ofFn_getD_eq_of_length
import Theorems.Thm_BKAR_Forest_paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ts : List ℝ) (hlen : ts.length = order.length) :
    F.paramsOfOrder order ts =
      (F.orderMeasurableEquivOfOrder horder).symm
        (fun i : Fin order.length => ts.getD i.val 0) := by
  calc
    F.paramsOfOrder order ts
        = F.paramsOfOrder order
            (List.ofFn fun i : Fin order.length => ts.getD i.val 0) := by
          rw [ofFn_getD_eq_of_length ts hlen]
    _ = (F.orderMeasurableEquivOfOrder horder).symm
          (fun i : Fin order.length => ts.getD i.val 0) := by
          exact F.paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm horder
            (fun i : Fin order.length => ts.getD i.val 0)
end BKAR.Forest
