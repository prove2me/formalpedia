-- Prove2me | solution 1 for Ehrhart.SimplexVolume.exists_centeredBody_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/0d9be11d-a631-480a-9b75-e88619d4984b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_Geometry_isCompact_centeredSimplex
import Theorems.Thm_Ehrhart_Geometry_convex_centeredSimplex
import Theorems.Thm_Ehrhart_Geometry_interior_centeredSimplex_nonempty
import Theorems.Thm_Ehrhart_Geometry_interiorLatticePoints_centeredSimplex
import Theorems.Thm_Ehrhart_SimplexVolume_normalizedVolume_centeredSimplex
import Theorems.Thm_Ehrhart_SimplexVolume_barycenter_centeredSimplex

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
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    ∃ K : CenteredBody n,
      normalizedVolume K.carrier = sharpConstant n := by
  refine ⟨{
    carrier := centeredSimplex n
    convex := Ehrhart.Geometry.convex_centeredSimplex n
    compact := Ehrhart.Geometry.isCompact_centeredSimplex n
    fullDimensional := Ehrhart.Geometry.interior_centeredSimplex_nonempty n hn
    centered := barycenter_centeredSimplex n
    uniqueInteriorLatticePoint :=
      Ehrhart.Geometry.interiorLatticePoints_centeredSimplex n hn
  }, normalizedVolume_centeredSimplex n hn⟩
end Ehrhart.SimplexVolume
