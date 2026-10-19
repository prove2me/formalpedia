-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.logarithmicPoint_insertNth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/d1023874-127e-4b5c-9e8a-a16afdd4549f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JointHolomorphicLaurentFourierCompatibility
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13915
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13918
namespace Ehrhart.JointHolomorphicLaurentFourierCompatibility
theorem _root_.solution {n : ℕ}
    (x : Space (n + 1))
    (i : Fin (n + 1)) (y : Fin n → ℝ) (t : ℝ) :
    logarithmicPoint x (i.insertNth t y) =
      fun j => if j = i
        then (x i : ℂ) / 2 +
          (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)
        else logarithmicPoint x (i.insertNth 0 y) j := by
  apply funext
  rw [i.forall_iff_succAbove]
  constructor
  · simp [logarithmicPoint]
  · intro j
    simp [logarithmicPoint, i.succAbove_ne]
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
