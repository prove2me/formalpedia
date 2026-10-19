-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.contDiff_angularSmoothPartitionBump
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/24b3dd10-d881-4fde-8041-ec9b5309bee3

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
theorem _root_.solution {m : ℕ∞} :
    ContDiff ℝ m angularSmoothPartitionBump := by
  unfold angularSmoothPartitionBump
  exact (Real.smoothTransition.contDiff.comp
    (contDiff_id.add contDiff_const)).sub
      Real.smoothTransition.contDiff
end Ehrhart.MatrixTorusBochnerBridge
