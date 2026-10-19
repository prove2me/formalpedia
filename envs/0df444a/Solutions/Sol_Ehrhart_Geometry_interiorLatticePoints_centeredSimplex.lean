-- Prove2me | solution 1 for Ehrhart.Geometry.interiorLatticePoints_centeredSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/7904c1e8-0974-4ab7-8a57-643ae553cbce

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_Geometry_zero_mem_interior_centeredSimplex
import Theorems.Thm_Ehrhart_Geometry_interior_integerPoint_eq_zero

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
    interiorLatticePoints (centeredSimplex n) = {0} := by
  ext z
  constructor
  · intro hz
    have hz' : integerPoint n z ∈
        interior (centeredSimplex n) := hz
    exact Set.mem_singleton_iff.mpr (interior_integerPoint_eq_zero hn z hz')
  · intro hz
    have hz' : z = 0 := Set.mem_singleton_iff.mp hz
    subst z
    change integerPoint n 0 ∈ interior (centeredSimplex n)
    have hzero : integerPoint n (0 : Fin n → ℤ) =
        (0 : Space n) := by
      funext i
      simp [integerPoint]
    rw [hzero]
    exact zero_mem_interior_centeredSimplex n hn
end Ehrhart.Geometry
