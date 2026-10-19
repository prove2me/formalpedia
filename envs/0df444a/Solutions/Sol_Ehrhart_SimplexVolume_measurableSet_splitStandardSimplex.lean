-- Prove2me | solution 1 for Ehrhart.SimplexVolume.measurableSet_splitStandardSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/eb2f9d2d-e1a1-41ad-b387-80a6d9398afd

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_Geometry_isClosed_standardSimplex
import Theorems.Thm_Ehrhart_SimplexVolume_splitStandardSimplex_eq_preimage

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
    MeasurableSet (splitStandardSimplex n) := by
  rw [splitStandardSimplex_eq_preimage]
  exact (Ehrhart.Geometry.isClosed_standardSimplex (n + 1)).measurableSet.preimage
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) 0).symm.measurable
end Ehrhart.SimplexVolume
