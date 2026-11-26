-- Prove2me | solution 1 for BKAR.Forest.interpolationLayerThreshold_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:20:15.881795+00:00
-- url     : https://prove2.me/submissions/223c3101-46b8-4f36-aa46-67fc014b943f

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_BKAR_ThresholdComponents
import Definitions.Def_BKAR_ThresholdLayerCake
import Theorems.Thm_BKAR_Forest_mem_thresholdComponent
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_Forest_self_mem_thresholdComponent
attribute [local simp] BKAR.Forest.mem_thresholdComponent
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.Forest.self_mem_thresholdComponent



set_option autoImplicit false
open BKAR
open scoped BigOperators
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (u : F.EdgeParam → ℝ) {i : ℕ}
    (hi : i < (F.interpolationLevels u).card - 1) :
    F.interpolationLayerThreshold u i =
      F.interpolationLevel u
        ⟨i + 1, by
          omega⟩ := by
  simp [interpolationLayerThreshold, hi]
end BKAR.Forest
