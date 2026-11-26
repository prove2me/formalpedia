-- Prove2me | solution 1 for BKAR.Forest.interpolationLevels_subset_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:20:19.995174+00:00
-- url     : https://prove2.me/submissions/3ebb3de4-545c-4d5f-aab6-4738a4dc68a9

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_BKAR_ThresholdComponents
import Definitions.Def_BKAR_ThresholdLayerCake
import Theorems.Thm_BKAR_Forest_mem_thresholdComponent
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_Forest_self_mem_thresholdComponent
import Theorems.Thm_BKAR_Forest_standardInterp_mem_Icc
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
    {x : ℝ} (hx : x ∈ F.interpolationLevels u) :
    0 ≤ x ∧ x ≤ 1 := by
  classical
  rw [interpolationLevels] at hx
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with rfl | rfl | ⟨e, he⟩
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩
  · rw [← he]
    exact F.standardInterp_mem_Icc u hu e
end BKAR.Forest
