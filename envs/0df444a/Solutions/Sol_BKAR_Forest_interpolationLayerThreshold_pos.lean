-- Prove2me | solution 1 for BKAR.Forest.interpolationLayerThreshold_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:49.918109+00:00
-- url     : https://prove2.me/submissions/4c755831-032a-4225-a996-a3eacc52b7fd

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_BKAR_ThresholdComponents
import Definitions.Def_BKAR_ThresholdLayerCake
import Theorems.Thm_BKAR_Forest_interpolationLevel_zero
import Theorems.Thm_BKAR_Forest_interpolationLayerThreshold_of_lt
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
    {i : ℕ} (hi : i < (F.interpolationLevels u).card - 1) :
    0 < F.interpolationLayerThreshold u i := by
  rw [F.interpolationLayerThreshold_of_lt u hi]
  have hlt :
      F.interpolationLevel u
          ⟨0, F.interpolationLevels_card_pos u⟩ <
        F.interpolationLevel u
          ⟨i + 1, by omega⟩ := by
    exact ((F.interpolationLevels u).orderEmbOfFin rfl).strictMono (by
      exact Nat.succ_pos i)
  simpa [F.interpolationLevel_zero u hu] using hlt
end BKAR.Forest
