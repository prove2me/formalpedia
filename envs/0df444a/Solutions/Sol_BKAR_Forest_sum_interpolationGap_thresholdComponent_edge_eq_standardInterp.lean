-- Prove2me | solution 1 for BKAR.Forest.sum_interpolationGap_thresholdComponent_edge_eq_standardInterp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:39:40.662371+00:00
-- url     : https://prove2.me/submissions/dfbfeebf-933a-4d09-8b21-8abdde09b6f7

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_BKAR_ThresholdComponents
import Definitions.Def_BKAR_ThresholdLayerCake
import Theorems.Thm_BKAR_Forest_standardInterp_mem_interpolationLevels
import Theorems.Thm_BKAR_Forest_interpolationLayerThreshold_pos
import Theorems.Thm_BKAR_Forest_interpolationLayerThreshold_le_one
import Theorems.Thm_BKAR_Forest_sum_interpolationGap_le_eq_of_mem_interpolationLevels
import Theorems.Thm_BKAR_Forest_le_standardInterp_iff_mem_thresholdComponent
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
    (e : Edge V) :
    (∑ i ∈ Finset.range ((F.interpolationLevels u).card - 1),
        if e.right ∈ F.thresholdComponent u
            (F.interpolationLayerThreshold u i) e.left then
          F.interpolationGap u i
        else
          0) = F.standardInterp u e := by
  classical
  rw [← F.sum_interpolationGap_le_eq_of_mem_interpolationLevels u hu
    (F.standardInterp_mem_interpolationLevels u e)]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hik : i < (F.interpolationLevels u).card - 1 :=
    Finset.mem_range.mp hi
  have hs0 : 0 < F.interpolationLayerThreshold u i :=
    F.interpolationLayerThreshold_pos u hu hik
  have hs1 : F.interpolationLayerThreshold u i ≤ 1 :=
    F.interpolationLayerThreshold_le_one u hu hik
  have hiff :
      F.interpolationLayerThreshold u i ≤ F.standardInterp u e ↔
        e.right ∈ F.thresholdComponent u
          (F.interpolationLayerThreshold u i) e.left :=
    F.le_standardInterp_iff_mem_thresholdComponent u hs0 hs1 e
  by_cases hle :
      F.interpolationLayerThreshold u i ≤ F.standardInterp u e
  · have hmem := hiff.mp hle
    simp [hle, hmem]
  · have hmem :
      e.right ∉ F.thresholdComponent u
        (F.interpolationLayerThreshold u i) e.left := by
      intro hmem
      exact hle (hiff.mpr hmem)
    simp [hle, hmem]
end BKAR.Forest
