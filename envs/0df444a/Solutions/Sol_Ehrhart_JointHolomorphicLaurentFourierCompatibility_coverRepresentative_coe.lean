-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.coverRepresentative_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/823da152-3606-4deb-b495-f222e0d0f7ea

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
    (F : TorusCharacters.LogSpace n → ℂ)
    (x t : Space n) (ht : t ∈ angularBox n) :
    coverRepresentative F x (fun i => (t i : UnitAddCircle)) =
      F (logarithmicPoint x t) := by
  unfold coverRepresentative logarithmicPoint
  congr 1
  funext i
  have hi : t i ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
    simpa using ht i (Set.mem_univ i)
  rw [AddCircle.equivIoc_coe_eq hi]
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
