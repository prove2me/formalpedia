-- Prove2me | solution 1 for BKAR.Forest.sum_interpolationGap_range_eq_interpolationLevel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:06.961081+00:00
-- url     : https://prove2.me/submissions/d1603a9d-e564-480a-b000-cb981f526c9a

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_BKAR_ThresholdComponents
import Definitions.Def_BKAR_ThresholdLayerCake
import Theorems.Thm_BKAR_Forest_interpolationGap_of_lt
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


section
namespace BKAR
open scoped BigOperators
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
private theorem interpolationLevelAux_of_lt
    (F : Forest V) (u : F.EdgeParam → ℝ) {i : ℕ}
    (hi : i < (F.interpolationLevels u).card) :
    interpolationLevelAux F u i = F.interpolationLevel u ⟨i, hi⟩ := by
  simp [interpolationLevelAux, hi]
end
end Forest
end BKAR
end

set_option autoImplicit false
open BKAR
open scoped BigOperators
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (u : F.EdgeParam → ℝ)
    {n : ℕ} (hn : n < (F.interpolationLevels u).card) :
    (∑ i ∈ Finset.range n, F.interpolationGap u i) =
      F.interpolationLevel u ⟨n, hn⟩ -
        F.interpolationLevel u
          ⟨0, F.interpolationLevels_card_pos u⟩ := by
  let f : ℕ → ℝ := interpolationLevelAux F u
  calc
    (∑ i ∈ Finset.range n, F.interpolationGap u i) =
        ∑ i ∈ Finset.range n, (f (i + 1) - f i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hin : i < n := Finset.mem_range.mp hi
          have hik : i < (F.interpolationLevels u).card - 1 := by
            omega
          rw [F.interpolationGap_of_lt u hik]
          change
            F.interpolationLevel u ⟨i + 1, by omega⟩ -
                F.interpolationLevel u ⟨i, by omega⟩ =
              interpolationLevelAux F u (i + 1) -
                interpolationLevelAux F u i
          rw [interpolationLevelAux_of_lt F u (i := i + 1) (by omega)]
          rw [interpolationLevelAux_of_lt F u (i := i) (by omega)]
    _ = f n - f 0 := Finset.sum_range_sub f n
    _ =
        F.interpolationLevel u ⟨n, hn⟩ -
          F.interpolationLevel u
            ⟨0, F.interpolationLevels_card_pos u⟩ := by
          change interpolationLevelAux F u n - interpolationLevelAux F u 0 =
            F.interpolationLevel u ⟨n, hn⟩ -
              F.interpolationLevel u
                ⟨0, F.interpolationLevels_card_pos u⟩
          rw [interpolationLevelAux_of_lt F u hn]
          rw [interpolationLevelAux_of_lt F u
            (F.interpolationLevels_card_pos u)]
end BKAR.Forest
