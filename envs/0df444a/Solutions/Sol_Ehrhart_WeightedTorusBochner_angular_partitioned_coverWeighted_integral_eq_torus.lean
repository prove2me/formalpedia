-- Prove2me | solution 1 for Ehrhart.WeightedTorusBochner.angular_partitioned_coverWeighted_integral_eq_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/196bf7b2-7579-4c6c-af84-c28240c182e5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_integral_coverWeightedMeasure
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_partitioned_coverWeighted_integral_eq_torus
import Theorems.Thm_Ehrhart_WeightedTorusDolbeault_continuous_angularCoverPotential
import Theorems.Thm_Ehrhart_WeightedTorusBochner_zeroSourceCoverWeightedMeasure
import Theorems.Thm_Ehrhart_WeightedTorusBochner_zeroSourceWeightedTorusMeasure
import Theorems.Thm_Ehrhart_WeightedTorusBochner_continuous_angularUnweightedTorusIntegrand
import Theorems.Thm_Ehrhart_WeightedTorusBochner_hasCompactSupport_angularUnweightedTorusIntegrand
import Theorems.Thm_Ehrhart_WeightedTorusBochner_integral_angularUnweightedTorusIntegrand_eq_weighted

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
    {f : LogTorus n → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    logarithmicCoverJacobianFactor n •
      (∫ z : TorusCharacters.LogSpace n,
        (coverAngularSmoothPartition z : ℂ) *
          f (complexTorusCoverProjection n z)
        ∂(coverWeightedMeasure (angularCoverPotential a))) =
      ∫ p : LogTorus n, f p ∂(angularWeightedTorusMeasure a) := by
  let g : LogTorus n → ℂ := angularUnweightedTorusIntegrand a f
  have hg : Continuous g :=
    continuous_angularUnweightedTorusIntegrand ha hf
  have hgc : HasCompactSupport g :=
    hasCompactSupport_angularUnweightedTorusIntegrand a hfc
  have hzero := partitioned_coverWeighted_integral_eq_torus
    (φ := fun _ : Space n => (0 : ℝ))
    continuous_const hg hgc
  rw [zeroSourceCoverWeightedMeasure,
    zeroSourceWeightedTorusMeasure] at hzero
  calc
    _ = logarithmicCoverJacobianFactor n •
        (∫ z : TorusCharacters.LogSpace n,
          (coverAngularSmoothPartition z : ℂ) *
            g (complexTorusCoverProjection n z)
          ∂(volume : Measure
            (TorusCharacters.LogSpace n))) := by
      apply congrArg
        (fun q : ℂ => logarithmicCoverJacobianFactor n • q)
      rw [integral_coverWeightedMeasure
        (continuous_angularCoverPotential ha)]
      apply integral_congr_ae
      filter_upwards [] with z
      simp [g, angularUnweightedTorusIntegrand,
        complexCoverWeight, coverWeight,
        angularCoverPotential, angularWeightedTorusDensity]
      ring
    _ = ∫ p : LogTorus n, g p
          ∂(sourceTorusBaseMeasure n) := hzero
    _ = _ := integral_angularUnweightedTorusIntegrand_eq_weighted
      ha f
end Ehrhart.WeightedTorusBochner
