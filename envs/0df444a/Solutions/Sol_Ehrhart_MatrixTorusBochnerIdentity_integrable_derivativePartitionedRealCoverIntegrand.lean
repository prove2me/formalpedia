-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.integrable_derivativePartitionedRealCoverIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/9e1bfb23-05e6-49d4-94ee-60255dc99354

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_continuous_derivativePartitionedRealCoverIntegrand
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_hasCompactSupport_derivativePartitionedRealCoverIntegrand

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
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (v : Space n) :
    Integrable (derivativePartitionedRealCoverIntegrand φ f v)
      (volume : Measure (Space n × Space n)) := by
  exact (continuous_derivativePartitionedRealCoverIntegrand
    hφ hf v).integrable_of_hasCompactSupport
      (hasCompactSupport_derivativePartitionedRealCoverIntegrand hfc v)
end Ehrhart.MatrixTorusBochnerIdentity
