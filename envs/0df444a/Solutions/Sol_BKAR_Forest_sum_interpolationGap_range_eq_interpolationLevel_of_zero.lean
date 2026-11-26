-- Prove2me | solution 1 for BKAR.Forest.sum_interpolationGap_range_eq_interpolationLevel_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:12:58.86346+00:00
-- url     : https://prove2.me/submissions/e4aa5029-f52e-4bad-8552-4893b3a7ee30

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_BKAR_ThresholdComponents
import Definitions.Def_BKAR_ThresholdLayerCake
import Theorems.Thm_BKAR_Forest_interpolationLevel_zero
import Theorems.Thm_BKAR_Forest_sum_interpolationGap_range_eq_interpolationLevel
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
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    {n : ℕ} (hn : n < (F.interpolationLevels u).card) :
    (∑ i ∈ Finset.range n, F.interpolationGap u i) =
      F.interpolationLevel u ⟨n, hn⟩ := by
  rw [F.sum_interpolationGap_range_eq_interpolationLevel u hn]
  rw [F.interpolationLevel_zero u hu]
  simp
end BKAR.Forest
