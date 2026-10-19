-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.binaryAngularPartitionSum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/12b22f63-01e6-46dc-8ed4-ae8e4ccb4ff7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_angularSmoothPartition_binary_sum

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
    {n : ℕ} (t : Space n)
    (hzero : ∀ i : Fin n, 0 ≤ t i)
    (hone : ∀ i : Fin n, t i ≤ 1) :
    binaryAngularPartitionSum n t = 1 := by
  unfold binaryAngularPartitionSum
  calc
    _ = ∑ q : Fin n → Bool,
      angularSmoothPartition
        (fun i => t i - if q i then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      funext i
      simp only [Pi.add_apply, binaryAngularFundamentalBase]
      split <;> ring
    _ = 1 := angularSmoothPartition_binary_sum t hzero hone
end Ehrhart.MatrixTorusBochnerIdentity
