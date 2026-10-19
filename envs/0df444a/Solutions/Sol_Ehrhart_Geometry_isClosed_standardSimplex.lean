-- Prove2me | solution 1 for Ehrhart.Geometry.isClosed_standardSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/f8556854-43c1-4d30-8e98-98a51505dfd5

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
    IsClosed (standardSimplex n) := by
  have hcoords :
      IsClosed (⋂ i : Fin n, {x : Space n | 0 ≤ x i}) :=
    isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have hsum : IsClosed {x : Space n | (∑ i, x i) ≤ 1} :=
    isClosed_le (continuous_coordinateSum n) continuous_const
  have hset : standardSimplex n =
      (⋂ i : Fin n, {x : Space n | 0 ≤ x i}) ∩
        {x : Space n | (∑ i, x i) ≤ 1} := by
    ext x
    simp [standardSimplex]
  rw [hset]
  exact hcoords.inter hsum
end Ehrhart.Geometry
