-- Prove2me | solution 1 for Ehrhart.Geometry.continuous_simplexDilation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/9ad73258-c6b8-4f73-9129-e42957974ad0

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    Continuous (simplexDilation n) := by
  apply continuous_pi
  intro i
  exact (continuous_const.mul (continuous_apply i)).sub continuous_const
end Ehrhart.Geometry
