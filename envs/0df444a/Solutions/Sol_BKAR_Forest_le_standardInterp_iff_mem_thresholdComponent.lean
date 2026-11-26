-- Prove2me | solution 1 for BKAR.Forest.le_standardInterp_iff_mem_thresholdComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:09.372918+00:00
-- url     : https://prove2.me/submissions/e43174df-259d-4676-a735-90c190a4805c

import Mathlib.Order.Partition.Finpartition
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Threshold
import Definitions.Def_BKAR_ThresholdComponents
import Theorems.Thm_BKAR_Forest_mem_thresholdComponent
import Theorems.Thm_BKAR_Forest_le_standardInterp_iff_thresholdConnected
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil


attribute [local simp] BKAR.Forest.mem_thresholdComponent

set_option autoImplicit false
open BKAR
open scoped BigOperators
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (e : Edge V) :
    s ≤ F.standardInterp u e ↔
      e.right ∈ F.thresholdComponent u s e.left := by
  rw [F.mem_thresholdComponent u s]
  exact F.le_standardInterp_iff_thresholdConnected u hs0 hs1 e
end BKAR.Forest
