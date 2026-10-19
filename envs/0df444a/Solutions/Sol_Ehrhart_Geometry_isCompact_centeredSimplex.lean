-- Prove2me | solution 1 for Ehrhart.Geometry.isCompact_centeredSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/1cbd6a70-f6ce-4e2f-bada-f3a7a0397ecc

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_Geometry_isCompact_standardSimplex
import Theorems.Thm_Ehrhart_Geometry_continuous_simplexDilation

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.Geometry
open Set MeasureTheory
open scoped BigOperators
namespace Ehrhart.Geometry
theorem _root_.solution (n : ℕ) :
    IsCompact (centeredSimplex n) := by
  exact (isCompact_standardSimplex n).image (continuous_simplexDilation n)
end Ehrhart.Geometry
