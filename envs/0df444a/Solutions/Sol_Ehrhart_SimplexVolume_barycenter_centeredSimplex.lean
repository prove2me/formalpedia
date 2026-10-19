-- Prove2me | solution 1 for Ehrhart.SimplexVolume.barycenter_centeredSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/66b0ad90-64de-4db8-802b-6e3b9829b90a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_Geometry_mem_centeredSimplex_iff
import Theorems.Thm_Ehrhart_Geometry_isCompact_centeredSimplex
import Theorems.Thm_Ehrhart_SimplexVolume_centeredSimplex_coordinate_tail_measure
import Theorems.Thm_Ehrhart_SimplexVolume_centered_integral_zero_of_coordinate_tails

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
    barycenter (centeredSimplex n) = 0 := by
  have hzero : (∫ y in centeredSimplex n, y) =
      (0 : Space n) :=
    centered_integral_zero_of_coordinate_tails
      (centeredSimplex n)
      (Ehrhart.Geometry.isCompact_centeredSimplex n)
      ((volume : Measure (Space n)).real
        (standardSimplex n))
      (fun _ => Ehrhart.Geometry.mem_centeredSimplex_iff)
      (fun i _ ht0 ht1 => centeredSimplex_coordinate_tail_measure
        (centeredSimplex n)
        (fun _ => Ehrhart.Geometry.mem_centeredSimplex_iff) i ht0 ht1)
  simp [barycenter, hzero]
end Ehrhart.SimplexVolume
