-- Prove2me | solution 1 for Ehrhart.Geometry.coordinateSum_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/6d8bc454-da64-455e-9057-2f761a93c3eb

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
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    Function.Surjective (coordinateSum n) := by
  classical
  intro t
  let i : Fin n := ⟨0, hn⟩
  refine ⟨fun j => if j = i then t else 0, ?_⟩
  simp [coordinateSum]
end Ehrhart.Geometry
