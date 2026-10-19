-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.angularSmoothPartitionBump_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/4b47751b-ef76-4409-926e-88a7c5f9662f

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
theorem _root_.solution (t : ℝ) :
    0 ≤ angularSmoothPartitionBump t := by
  unfold angularSmoothPartitionBump
  exact sub_nonneg.mpr
    (Real.smoothTransition.monotone (by linarith))
end Ehrhart.MatrixTorusBochnerBridge
