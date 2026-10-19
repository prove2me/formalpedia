-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.angularSmoothPartition_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/29077ceb-7106-4a30-81e7-70a286a33061

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_angularSmoothPartitionBump_nonneg

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
    {n : ℕ} (t : Space n) :
    0 ≤ angularSmoothPartition t := by
  unfold angularSmoothPartition
  exact Finset.prod_nonneg
    (fun i _ => angularSmoothPartitionBump_nonneg (t i))
end Ehrhart.MatrixTorusBochnerBridge
