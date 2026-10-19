-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.hasCompactSupport_unweightedSourceTorusIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/cbc67f77-b2e2-42c9-b1bc-cee85357f530

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
    {n : ℕ} {φ : Space n → ℝ}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hfc : HasCompactSupport f) :
    HasCompactSupport (unweightedSourceTorusIntegrand φ f) := by
  exact hfc.mul_left
end Ehrhart.MatrixTorusBochnerBridge
