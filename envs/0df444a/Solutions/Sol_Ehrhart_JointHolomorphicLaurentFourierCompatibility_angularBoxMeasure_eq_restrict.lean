-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.angularBoxMeasure_eq_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/6eb31489-a041-434b-8405-b7175624e9f1

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
theorem _root_.solution (n : ℕ) :
    angularBoxMeasure n =
      (volume : Measure (Space n)).restrict (angularBox n) := by
  unfold angularBoxMeasure angularBox
  rw [MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi]
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
