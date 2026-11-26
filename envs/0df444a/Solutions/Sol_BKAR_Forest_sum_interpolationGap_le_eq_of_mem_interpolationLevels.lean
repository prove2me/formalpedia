-- Prove2me | solution 1 for BKAR.Forest.sum_interpolationGap_le_eq_of_mem_interpolationLevels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:14:06.941331+00:00
-- url     : https://prove2.me/submissions/6b22c0b6-5e8d-4eee-a924-9b80d1954028

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_BKAR_ThresholdComponents
import Definitions.Def_BKAR_ThresholdLayerCake
import Theorems.Thm_BKAR_Forest_interpolationLayerThreshold_of_lt
import Theorems.Thm_BKAR_Forest_sum_interpolationGap_range_eq_interpolationLevel_of_zero
import Theorems.Thm_BKAR_ForestIndex_ext
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
    {x : ℝ} (hx : x ∈ F.interpolationLevels u) :
    (∑ i ∈ Finset.range ((F.interpolationLevels u).card - 1),
        if F.interpolationLayerThreshold u i ≤ x then
          F.interpolationGap u i
        else
          0) = x := by
  classical
  let n : Fin (F.interpolationLevels u).card :=
    ((F.interpolationLevels u).orderIsoOfFin rfl).symm ⟨x, hx⟩
  have hxlevel : F.interpolationLevel u n = x := by
    rw [interpolationLevel]
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp [n]
  have hfilter :
      (Finset.range ((F.interpolationLevels u).card - 1)).filter
          (fun i => F.interpolationLayerThreshold u i ≤ x) =
        Finset.range n.1 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, hle⟩
      have hthr :
          F.interpolationLayerThreshold u i =
            F.interpolationLevel u ⟨i + 1, by omega⟩ :=
        F.interpolationLayerThreshold_of_lt u hi
      have hle' :
          F.interpolationLevel u ⟨i + 1, by omega⟩ ≤
            F.interpolationLevel u n := by
        calc
          F.interpolationLevel u ⟨i + 1, by omega⟩ =
              F.interpolationLayerThreshold u i := hthr.symm
          _ ≤ x := hle
          _ = F.interpolationLevel u n := hxlevel.symm
      have hnat : i + 1 ≤ n.1 := by
        have hfin : (⟨i + 1, by omega⟩ :
            Fin (F.interpolationLevels u).card) ≤ n := by
          exact ((F.interpolationLevels u).orderEmbOfFin rfl).le_iff_le.mp
            (by simpa [interpolationLevel] using hle')
        exact hfin
      omega
    · intro hi
      have hik : i < (F.interpolationLevels u).card - 1 := by
        have hn : n.1 < (F.interpolationLevels u).card := n.2
        omega
      refine ⟨hik, ?_⟩
      have hleNat : i + 1 ≤ n.1 := by omega
      have hle' :
          F.interpolationLevel u ⟨i + 1, by omega⟩ ≤
            F.interpolationLevel u n := by
        exact ((F.interpolationLevels u).orderEmbOfFin rfl).monotone
          (by
            exact hleNat)
      calc
        F.interpolationLayerThreshold u i =
            F.interpolationLevel u ⟨i + 1, by omega⟩ :=
          F.interpolationLayerThreshold_of_lt u hik
        _ ≤ F.interpolationLevel u n := hle'
        _ = x := hxlevel
  rw [← Finset.sum_filter]
  rw [hfilter]
  rw [F.sum_interpolationGap_range_eq_interpolationLevel_of_zero u hu n.2]
  exact hxlevel
end BKAR.Forest
