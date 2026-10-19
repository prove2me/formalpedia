-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.contDiff_coverAngularSmoothPartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/a80c0582-2e9e-4e39-bc65-54ad948e589d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_contDiff_angularSmoothPartition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerBridge
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerBridge
theorem _root_.solution
    {n : ℕ} {m : ℕ∞} :
    ContDiff ℝ m (coverAngularSmoothPartition (n := n)) := by
  unfold coverAngularSmoothPartition
  exact contDiff_angularSmoothPartition.comp (by fun_prop)
end Ehrhart.MatrixTorusBochnerBridge
