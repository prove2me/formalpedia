-- Prove2me | solution 1 for Ehrhart.SimplexVolume.normalizedVolume_splitStandardSimplex_fiber_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/ccc3a1b7-de8a-4f31-8e94-e65872c0d9c4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_SimplexVolume_splitStandardSimplex_fiber_of_mem_Ico
import Theorems.Thm_Ehrhart_SimplexVolume_splitStandardSimplex_fiber_eq_empty
import Theorems.Thm_Ehrhart_SimplexVolume_normalizedVolume_smul_standardSimplex

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.SimplexVolume
open Set MeasureTheory
open scoped BigOperators ENNReal Pointwise
namespace Ehrhart.SimplexVolume
theorem _root_.solution (n : ℕ) :
    (fun t : ℝ => normalizedVolume
      (Prod.mk t ⁻¹' splitStandardSimplex n)) =ᵐ[volume]
        (Set.Icc (0 : ℝ) 1).indicator
          (fun t => (1 - t) ^ n *
            normalizedVolume (standardSimplex n)) := by
  filter_upwards [(volume : Measure ℝ).ae_ne 1] with t ht
  by_cases ht0 : 0 ≤ t
  · by_cases ht1 : t < 1
    · have hi : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0, ht1.le⟩
      rw [Set.indicator_of_mem hi,
        splitStandardSimplex_fiber_of_mem_Ico n ⟨ht0, ht1⟩,
        normalizedVolume_smul_standardSimplex n (1 - t)
          (sub_nonneg.mpr ht1.le)]
    · have hgt : 1 < t :=
        lt_of_le_of_ne (le_of_not_gt ht1) ht.symm
      have hnot : t ∉ Set.Icc (0 : ℝ) 1 := by
        intro h
        linarith [h.2]
      rw [Set.indicator_of_notMem hnot,
        splitStandardSimplex_fiber_eq_empty n (Or.inr hgt)]
      simp [normalizedVolume]
  · have hneg : t < 0 := lt_of_not_ge ht0
    have hnot : t ∉ Set.Icc (0 : ℝ) 1 := by
      intro h
      linarith [h.1]
    rw [Set.indicator_of_notMem hnot,
      splitStandardSimplex_fiber_eq_empty n (Or.inl hneg)]
    simp [normalizedVolume]
end Ehrhart.SimplexVolume
