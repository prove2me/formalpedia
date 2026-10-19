-- Prove2me | solution 1 for Ehrhart.Geometry.isOpen_strict_centered_halfspaces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/b5c1b628-9cd3-4bac-b045-b0cf797ed335

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_Geometry_continuous_coordinateSum

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
    IsOpen {x : Space n |
      (∀ i, -(1 : ℝ) < x i) ∧ (∑ i, x i) < 1} := by
  have hcoords :
      IsOpen (⋂ i : Fin n, {x : Space n | -(1 : ℝ) < x i}) :=
    isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hsum : IsOpen {x : Space n | (∑ i, x i) < 1} :=
    isOpen_lt (continuous_coordinateSum n) continuous_const
  have hset :
      {x : Space n |
        (∀ i, -(1 : ℝ) < x i) ∧ (∑ i, x i) < 1} =
        (⋂ i : Fin n, {x : Space n | -(1 : ℝ) < x i}) ∩
          {x : Space n | (∑ i, x i) < 1} := by
    ext x
    simp
  rw [hset]
  exact hcoords.inter hsum
end Ehrhart.Geometry
