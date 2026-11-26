-- Prove2me | solution 1 for BKAR.Forest.interpolationLevels_max_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:10:09.682486+00:00
-- url     : https://prove2.me/submissions/977be646-09e4-4848-bf51-5f67645efebe

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_BKAR_ThresholdComponents
import Definitions.Def_BKAR_ThresholdLayerCake
import Theorems.Thm_BKAR_Forest_interpolationLevels_subset_Icc

set_option autoImplicit false
open BKAR
open scoped BigOperators
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) :
    (F.interpolationLevels u).max'
        ⟨1, F.one_mem_interpolationLevels u⟩ = 1 := by
  apply le_antisymm
  · exact (F.interpolationLevels_subset_Icc u hu
      ((F.interpolationLevels u).max'_mem _)).2
  · exact (F.interpolationLevels u).le_max' 1
      (F.one_mem_interpolationLevels u)
end BKAR.Forest
