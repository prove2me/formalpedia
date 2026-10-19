-- Prove2me | solution 1 for Ehrhart.WeightedTorusBochner.hasCompactSupport_angularUnweightedTorusIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/35547e85-0e7d-42f2-9923-37592a4b3569

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
theorem _root_.solution {n : ℕ}
    (a : LogTorus n → ℝ)
    {f : LogTorus n → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (angularUnweightedTorusIntegrand a f) :=
  hf.mul_left
end Ehrhart.WeightedTorusBochner
