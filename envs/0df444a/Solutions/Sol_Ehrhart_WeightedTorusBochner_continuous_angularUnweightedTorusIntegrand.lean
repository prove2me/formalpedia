-- Prove2me | solution 1 for Ehrhart.WeightedTorusBochner.continuous_angularUnweightedTorusIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/2846c339-f308-477c-a8e5-b9bd84a4b23c

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
    {a : LogTorus n → ℝ} (ha : Continuous a)
    {f : LogTorus n → ℂ} (hf : Continuous f) :
    Continuous (angularUnweightedTorusIntegrand a f) :=
  (Complex.continuous_ofReal.comp
    (continuous_angularWeightedTorusDensity ha)).mul hf
end Ehrhart.WeightedTorusBochner
