-- Prove2me | solution 1 for BKAR.Forest.paramsOfOrder_mem_unitCube_of_orderedSimplexParams
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:30:19.395205+00:00
-- url     : https://prove2.me/submissions/c8eac74d-c6d7-4080-841e-74256198f97b

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Theorems.Thm_BKAR_Forest_mem_unitCube_iff
import Theorems.Thm_BKAR_OrderedSimplexParams_le_top_of_mem
import Theorems.Thm_BKAR_OrderedSimplexParams_nonneg_of_mem


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (order : List (Edge V)) {ts : List ℝ}
    (hts : OrderedSimplexParams 1 ts) :
    F.paramsOfOrder order ts ∈ F.unitCube := by
  rw [mem_unitCube_iff]
  intro e
  rw [paramsOfOrder]
  by_cases hidx : order.idxOf e.val < ts.length
  · rw [List.getD_eq_getElem _ _ hidx]
    constructor
    · exact OrderedSimplexParams.nonneg_of_mem hts
        (List.getElem_mem hidx)
    · exact OrderedSimplexParams.le_top_of_mem hts
        (List.getElem_mem hidx)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hidx)]
    norm_num
end BKAR.Forest
