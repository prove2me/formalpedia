-- Prove2me | solution 1 for BKAR.Forest.mem_thresholdComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:18:01.711056+00:00
-- url     : https://prove2.me/submissions/b1f987fd-54ae-40a8-b476-e0e784362ab9

import Mathlib.Order.Partition.Finpartition
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Threshold
import Definitions.Def_BKAR_ThresholdComponents
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil



set_option autoImplicit false
open BKAR
open scoped BigOperators
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) (u : F.EdgeParam → ℝ)
    (s : ℝ) (i j : V) :
    j ∈ F.thresholdComponent u s i ↔
      F.thresholdConnected u s i j := by
  classical
  simpa [thresholdComponent, thresholdPartition, thresholdSetoid] using!
    (Finpartition.mem_part_ofSetoid_iff_rel
      (s := F.thresholdSetoid u s) (a := i) (b := j))
end BKAR.Forest
