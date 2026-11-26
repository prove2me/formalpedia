-- Prove2me | solution 1 for BKAR.Forest.interpolationLayerThreshold_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:10:43.488715+00:00
-- url     : https://prove2.me/submissions/b408ebdf-77cf-4839-b53e-a367eef18b18

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_BKAR_ThresholdComponents
import Definitions.Def_BKAR_ThresholdLayerCake
import Theorems.Thm_BKAR_Forest_interpolationLevels_subset_Icc
import Theorems.Thm_BKAR_Forest_interpolationLayerThreshold_of_lt

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
    {i : ℕ} (hi : i < (F.interpolationLevels u).card - 1) :
    F.interpolationLayerThreshold u i ≤ 1 := by
  rw [F.interpolationLayerThreshold_of_lt u hi]
  exact (F.interpolationLevels_subset_Icc u hu
    ((F.interpolationLevels u).orderEmbOfFin_mem rfl ⟨i + 1, by omega⟩)).2
end BKAR.Forest
