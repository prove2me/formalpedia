-- Prove2me | solution 1 for BKAR.Forest.sum_thresholdPartition_parts_indicator_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:38:38.669164+00:00
-- url     : https://prove2.me/submissions/9d7f3756-f9e5-463b-8314-bf60516e5498

import Mathlib.Order.Partition.Finpartition
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Threshold
import Definitions.Def_BKAR_ThresholdComponents
import Theorems.Thm_BKAR_Finpartition_sum_parts_indicator_pair
import Theorems.Thm_BKAR_Forest_mem_thresholdComponent
import Theorems.Thm_BKAR_Forest_self_mem_thresholdComponent
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil


attribute [local simp] BKAR.Forest.mem_thresholdComponent
attribute [local simp] BKAR.Forest.self_mem_thresholdComponent

set_option autoImplicit false
open BKAR
open scoped BigOperators
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (u : F.EdgeParam → ℝ) (s r : ℝ) (z w : V) :
    (∑ c : {c : Finset V // c ∈ (F.thresholdPartition u s).parts},
        if z ∈ c.1 ∧ w ∈ c.1 then r else 0) =
      if w ∈ F.thresholdComponent u s z then r else 0 := by
  simpa [thresholdComponent] using!
    (Finpartition.sum_parts_indicator_pair
      (P := F.thresholdPartition u s) (r := r) (z := z) (w := w))
end BKAR.Forest
