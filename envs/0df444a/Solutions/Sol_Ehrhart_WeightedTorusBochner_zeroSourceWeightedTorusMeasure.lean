-- Prove2me | solution 1 for Ehrhart.WeightedTorusBochner.zeroSourceWeightedTorusMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/66a9d7b4-4f7a-403f-8484-fb7c5c8901dc

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusBochner
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.WeightedTorusBochner
theorem _root_.solution {n : ℕ} :
    weightedTorusMeasure 1 (fun _ : Space n => (0 : ℝ)) =
      sourceTorusBaseMeasure n := by
  rw [weightedTorusMeasure_eq_withDensity 1 continuous_const]
  simp [sourceTorusBaseMeasure, radialWeight]
end Ehrhart.WeightedTorusBochner
