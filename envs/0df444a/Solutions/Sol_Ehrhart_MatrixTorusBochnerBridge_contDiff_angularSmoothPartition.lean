-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.contDiff_angularSmoothPartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/7b7ab56a-5d9f-482d-aa5c-836e1a0bc6ef

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_contDiff_angularSmoothPartitionBump

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
    ContDiff ℝ m (angularSmoothPartition (n := n)) := by
  unfold angularSmoothPartition
  apply contDiff_prod
  intro i _
  apply contDiff_angularSmoothPartitionBump.comp
  fun_prop
end Ehrhart.MatrixTorusBochnerBridge
