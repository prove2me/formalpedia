-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.angularSmoothPartitionBump_add_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/66e30714-29e4-4b7b-9286-156a94acbe69

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    {t : ℝ} (hzero : 0 ≤ t) (hone : t ≤ 1) :
    angularSmoothPartitionBump t +
      angularSmoothPartitionBump (t - 1) = 1 := by
  have hplus : Real.smoothTransition (t + 1) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  have hminus : Real.smoothTransition (t - 1) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have ht : t - 1 + 1 = t := by ring
  unfold angularSmoothPartitionBump
  rw [hplus, ht, hminus]
  ring
end Ehrhart.MatrixTorusBochnerBridge
