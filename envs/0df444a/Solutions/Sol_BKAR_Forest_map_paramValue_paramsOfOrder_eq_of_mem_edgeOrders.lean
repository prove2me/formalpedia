-- Prove2me | solution 1 for BKAR.Forest.map_paramValue_paramsOfOrder_eq_of_mem_edgeOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:31:21.35602+00:00
-- url     : https://prove2.me/submissions/d0cff12c-2763-4f8f-b2ce-6c99bc4e4979

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Theorems.Thm_BKAR_Forest_map_paramValue_paramsOfOrder_eq_of_nodup_of_forall_mem
import Theorems.Thm_BKAR_Forest_nodup_of_mem_edgeOrders
import Theorems.Thm_BKAR_Forest_toFinset_eq_of_mem_edgeOrders


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    {ts : List ℝ} (hlen : ts.length = order.length) :
    order.map (F.paramValue (F.paramsOfOrder order ts)) = ts := by
  exact
    F.map_paramValue_paramsOfOrder_eq_of_nodup_of_forall_mem order
      (F.nodup_of_mem_edgeOrders horder)
      (by
        intro e he
        have hset := F.toFinset_eq_of_mem_edgeOrders horder
        rw [← hset]
        exact List.mem_toFinset.mpr he)
      hlen
end BKAR.Forest
