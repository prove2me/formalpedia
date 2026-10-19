-- Prove2me | solution 1 for Ehrhart.WeightedTorusBochner.integral_angularUnweightedTorusIntegrand_eq_weighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/3431165b-b960-43d2-b7ff-ddc5e00ac0bd

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
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (f : LogTorus n → ℂ) :
    (∫ p : LogTorus n,
      angularUnweightedTorusIntegrand a f p
        ∂(sourceTorusBaseMeasure n)) =
      ∫ p : LogTorus n, f p ∂(angularWeightedTorusMeasure a) := by
  have hm : Measurable
      (fun p : LogTorus n =>
        ENNReal.ofReal (angularWeightedTorusDensity a p)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_angularWeightedTorusDensity ha).measurable
  rw [angularWeightedTorusMeasure,
    integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall fun p => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with p
  simp [angularUnweightedTorusIntegrand,
    angularWeightedTorusDensity, Complex.real_smul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
end Ehrhart.WeightedTorusBochner
