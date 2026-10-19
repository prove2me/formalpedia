-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.contDiff_binaryAngularPartitionSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/87bdb860-26c4-4041-b3c2-70359bffd2c5

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
open Ehrhart.MatrixTorusBochnerIdentity
open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerIdentity
theorem _root_.solution
    {n : ℕ} {m : ℕ∞} :
    ContDiff ℝ m (binaryAngularPartitionSum n) := by
  unfold binaryAngularPartitionSum
  apply ContDiff.sum
  intro q _
  exact contDiff_angularSmoothPartition.comp
    (contDiff_const.add contDiff_id)
end Ehrhart.MatrixTorusBochnerIdentity
