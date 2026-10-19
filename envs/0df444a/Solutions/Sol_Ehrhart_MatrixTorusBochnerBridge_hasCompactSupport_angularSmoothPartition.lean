-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.hasCompactSupport_angularSmoothPartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/7a7994d0-bda8-41c6-849d-94673436cb2e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_angularSmoothPartitionBump_zero_of_le
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_angularSmoothPartitionBump_zero_of_ge

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
    {n : ℕ} :
    HasCompactSupport (angularSmoothPartition (n := n)) := by
  let Q : Set (Space n) :=
    Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)
  have hQ : IsCompact Q :=
    isCompact_univ_pi (fun _ : Fin n => isCompact_Icc)
  apply hQ.of_isClosed_subset
    (isClosed_tsupport (angularSmoothPartition (n := n)))
  apply closure_minimal
  · intro t ht
    change angularSmoothPartition t ≠ 0 at ht
    intro i _
    have hi : angularSmoothPartitionBump (t i) ≠ 0 := by
      intro hz
      apply ht
      unfold angularSmoothPartition
      exact Finset.prod_eq_zero (Finset.mem_univ i) hz
    constructor
    · by_contra hn
      exact hi (angularSmoothPartitionBump_zero_of_le
        (le_of_lt (lt_of_not_ge hn)))
    · by_contra hn
      exact hi (angularSmoothPartitionBump_zero_of_ge
        (le_of_lt (lt_of_not_ge hn)))
  · exact hQ.isClosed
end Ehrhart.MatrixTorusBochnerBridge
