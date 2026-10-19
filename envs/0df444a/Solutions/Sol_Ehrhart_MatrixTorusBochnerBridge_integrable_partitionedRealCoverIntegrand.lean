-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.integrable_partitionedRealCoverIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/4439889a-8151-4bb8-9dc0-6ac1c557a4f9

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_continuous_partitionedRealCoverIntegrand
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_hasCompactSupport_partitionedRealCoverIntegrand

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
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    Integrable (partitionedRealCoverIntegrand φ f)
      (volume : Measure (Space n × Space n)) := by
  exact (continuous_partitionedRealCoverIntegrand hφ hf).integrable_of_hasCompactSupport
    (hasCompactSupport_partitionedRealCoverIntegrand hfc)
end Ehrhart.MatrixTorusBochnerBridge
