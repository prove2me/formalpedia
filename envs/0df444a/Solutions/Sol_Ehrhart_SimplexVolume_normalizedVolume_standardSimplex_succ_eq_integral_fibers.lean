-- Prove2me | solution 1 for Ehrhart.SimplexVolume.normalizedVolume_standardSimplex_succ_eq_integral_fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/1961294d-b999-4cf2-a12e-05fb3bed6414

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_Geometry_isCompact_standardSimplex
import Theorems.Thm_Ehrhart_SimplexVolume_measurableSet_splitStandardSimplex
import Theorems.Thm_Ehrhart_SimplexVolume_volume_splitStandardSimplex

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
theorem _root_.solution
    (n : ℕ) :
    normalizedVolume (standardSimplex (n + 1)) =
      ∫ t : ℝ, normalizedVolume
        (Prod.mk t ⁻¹' splitStandardSimplex n) := by
  have hmeas := measurableSet_splitStandardSimplex n
  have hfinite :
      (volume : Measure (ℝ × Space n))
          (splitStandardSimplex n) ≠ ∞ := by
    rw [volume_splitStandardSimplex n]
    exact (Ehrhart.Geometry.isCompact_standardSimplex (n + 1)).measure_ne_top
  unfold normalizedVolume
  calc
    ((volume : Measure (Space (n + 1)))
        (standardSimplex (n + 1))).toReal =
      ((volume : Measure (ℝ × Space n))
        (splitStandardSimplex n)).toReal := by
          rw [volume_splitStandardSimplex n]
    _ =
      (((volume : Measure ℝ).prod (volume : Measure (Space n)))
        (splitStandardSimplex n)).toReal := by
          rfl
    _ = (∫⁻ t : ℝ,
      (volume : Measure (Space n))
        (Prod.mk t ⁻¹' splitStandardSimplex n)).toReal := by
          rw [MeasureTheory.Measure.prod_apply hmeas]
    _ = ∫ t : ℝ,
      ((volume : Measure (Space n))
        (Prod.mk t ⁻¹' splitStandardSimplex n)).toReal := by
          symm
          exact MeasureTheory.integral_toReal
            (measurable_measure_prodMk_left hmeas).aemeasurable
            (MeasureTheory.Measure.ae_measure_lt_top hmeas hfinite)
end Ehrhart.SimplexVolume
