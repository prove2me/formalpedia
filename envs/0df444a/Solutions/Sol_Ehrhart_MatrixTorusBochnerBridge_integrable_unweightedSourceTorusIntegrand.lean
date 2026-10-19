-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.integrable_unweightedSourceTorusIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/078de81a-6535-496e-8423-6b6d34e81393

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_continuous_unweightedSourceTorusIntegrand
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_hasCompactSupport_unweightedSourceTorusIntegrand

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
    Integrable (unweightedSourceTorusIntegrand φ f)
      ((volume : Measure (Space n)).prod
        (angularMeasure n)) := by
  let : IsLocallyFiniteMeasure
      ((volume : Measure (Space n)).prod
        (angularMeasure n)) := by
    infer_instance
  exact (continuous_unweightedSourceTorusIntegrand hφ hf).integrable_of_hasCompactSupport
    (hasCompactSupport_unweightedSourceTorusIntegrand hfc)
end Ehrhart.MatrixTorusBochnerBridge
