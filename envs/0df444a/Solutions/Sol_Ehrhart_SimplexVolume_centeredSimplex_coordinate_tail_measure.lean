-- Prove2me | solution 1 for Ehrhart.SimplexVolume.centeredSimplex_coordinate_tail_measure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/8f8dfcea-c4a4-4432-a0fb-68a22c3e8af0

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_SimplexVolume_centeredSimplex_coordinate_tail

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
theorem _root_.solution {n : ℕ}
    (T : Set (Space n))
    (hT : ∀ y, y ∈ T ↔
      (∀ j, -(1 : ℝ) ≤ y j) ∧ (∑ j, y j) ≤ 1)
    (i : Fin n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < (n : ℝ) + 1) :
    ((volume : Measure (Space n)).restrict T).real
        {y : Space n | t ≤ y i + 1} =
      ((n : ℝ) + 1 - t) ^ n *
        (volume : Measure (Space n)).real
          (standardSimplex n) := by
  have hm : MeasurableSet {y : Space n | t ≤ y i + 1} :=
    (isClosed_le continuous_const
      ((continuous_apply i).add continuous_const)).measurableSet
  rw [measureReal_def, Measure.restrict_apply hm]
  have hset : {y : Space n | t ≤ y i + 1} ∩ T =
      {y : Space n | y ∈ T ∧ t ≤ y i + 1} := by
    ext y
    simp [and_comm]
  rw [hset, centeredSimplex_coordinate_tail T hT i ht0 ht1]
  simp only [Set.image_add_right, measure_preimage_add_right,
    Measure.addHaar_smul_of_nonneg (volume : Measure (Space n))
      (sub_nonneg.mpr ht1.le), Module.finrank_fin_fun,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (pow_nonneg (sub_nonneg.mpr ht1.le) n)]
  rfl
end Ehrhart.SimplexVolume
