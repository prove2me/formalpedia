-- Prove2me | solution 1 for BKAR.Forest.paramsOfOrder_mem_orderedCubeSimplex_of_mem_edgeOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:56.394836+00:00
-- url     : https://prove2.me/submissions/72a437ff-5a06-48e9-badf-e6fcd01f61da

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Theorems.Thm_BKAR_Forest_mem_orderedCubeSimplex_iff
import Theorems.Thm_BKAR_Forest_paramsOfOrder_mem_unitCube_of_orderedSimplexParams
import Theorems.Thm_BKAR_Forest_map_paramValue_paramsOfOrder_eq_of_mem_edgeOrders

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    {ts : List ℝ} (hts : OrderedSimplexParams 1 ts)
    (hlen : ts.length = order.length) :
    F.paramsOfOrder order ts ∈ F.orderedCubeSimplex order := by
  rw [mem_orderedCubeSimplex_iff]
  constructor
  · exact F.paramsOfOrder_mem_unitCube_of_orderedSimplexParams order hts
  · rw [F.map_paramValue_paramsOfOrder_eq_of_mem_edgeOrders horder hlen]
    exact hts
end BKAR.Forest
