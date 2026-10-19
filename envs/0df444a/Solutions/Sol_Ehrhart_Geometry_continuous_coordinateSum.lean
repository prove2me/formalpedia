-- Prove2me | solution 1 for Ehrhart.Geometry.continuous_coordinateSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/52990b9d-72fd-4d2a-8dd2-67b6de21ca7a

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
    Continuous (coordinateSum n) := by
  exact continuous_finsetSum Finset.univ (fun i _ => continuous_apply i)
end Ehrhart.Geometry
