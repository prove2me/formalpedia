-- Prove2me | solution 1 for BKAR.Forest.sum_interpolationGap_thresholdComponent_diag_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:39:57.7088+00:00
-- url     : https://prove2.me/submissions/f6396dd9-47da-4382-918f-7d1e62cedf6d

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_BKAR_ThresholdComponents
import Definitions.Def_BKAR_ThresholdLayerCake
import Theorems.Thm_BKAR_Forest_sum_interpolationGap_range_last_eq_one
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
    (z : V) :
    (∑ i ∈ Finset.range ((F.interpolationLevels u).card - 1),
        if z ∈ F.thresholdComponent u
            (F.interpolationLayerThreshold u i) z then
          F.interpolationGap u i
        else
          0) = 1 := by
  calc
    (∑ i ∈ Finset.range ((F.interpolationLevels u).card - 1),
        if z ∈ F.thresholdComponent u
            (F.interpolationLayerThreshold u i) z then
          F.interpolationGap u i
        else
          0) =
          ∑ i ∈ Finset.range ((F.interpolationLevels u).card - 1),
          F.interpolationGap u i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          have hmem :
              z ∈ F.thresholdComponent u
                (F.interpolationLayerThreshold u i) z :=
            F.self_mem_thresholdComponent u
              (F.interpolationLayerThreshold u i) z
          simp [hmem]
    _ = 1 := F.sum_interpolationGap_range_last_eq_one u hu
end BKAR.Forest
