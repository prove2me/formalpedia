-- Prove2me | solution 1 for BKAR.Forest.interpolationLevels_min_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:47.07034+00:00
-- url     : https://prove2.me/submissions/676762b9-35ac-44f4-a78b-5c8376412178

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
    (F.interpolationLevels u).min'
        ⟨0, F.zero_mem_interpolationLevels u⟩ = 0 := by
  apply le_antisymm
  · exact (F.interpolationLevels u).min'_le 0
      (F.zero_mem_interpolationLevels u)
  · exact (F.interpolationLevels_subset_Icc u hu
      ((F.interpolationLevels u).min'_mem _)).1
end BKAR.Forest
