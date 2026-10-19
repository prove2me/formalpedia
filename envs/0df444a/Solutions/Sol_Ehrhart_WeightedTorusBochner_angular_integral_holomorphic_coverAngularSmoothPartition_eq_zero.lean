-- Prove2me | solution 1 for Ehrhart.WeightedTorusBochner.angular_integral_holomorphic_coverAngularSmoothPartition_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/377cb17a-3f33-49f9-b64a-a871b9006df4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_integral_coverWeightedMeasure
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_integral_holomorphicCoordinate_coverAngularSmoothPartition_mul_lift_eq_zero
import Theorems.Thm_Ehrhart_WeightedTorusDolbeault_continuous_angularCoverPotential
import Theorems.Thm_Ehrhart_WeightedTorusBochner_zeroSourceCoverWeightedMeasure
import Theorems.Thm_Ehrhart_WeightedTorusBochner_continuous_angularUnweightedTorusIntegrand
import Theorems.Thm_Ehrhart_WeightedTorusBochner_hasCompactSupport_angularUnweightedTorusIntegrand

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
    (hfc : HasCompactSupport f) (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      holomorphicCoordinate
        (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
        f (complexTorusCoverProjection n z)
      ∂(coverWeightedMeasure (angularCoverPotential a))) = 0 := by
  let g : LogTorus n → ℂ := angularUnweightedTorusIntegrand a f
  have hg : Continuous g :=
    continuous_angularUnweightedTorusIntegrand ha hf
  have hgc : HasCompactSupport g :=
    hasCompactSupport_angularUnweightedTorusIntegrand a hfc
  have hz :=
    integral_holomorphicCoordinate_coverAngularSmoothPartition_mul_lift_eq_zero
      (φ := fun _ : Space n => (0 : ℝ))
      continuous_const hg hgc j
  rw [zeroSourceCoverWeightedMeasure] at hz
  rw [integral_coverWeightedMeasure
    (continuous_angularCoverPotential ha)]
  calc
    _ = ∫ z : TorusCharacters.LogSpace n,
      holomorphicCoordinate
        (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
        g (complexTorusCoverProjection n z)
      ∂(volume : Measure (TorusCharacters.LogSpace n)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp [g, angularUnweightedTorusIntegrand,
        complexCoverWeight, coverWeight,
        angularCoverPotential, angularWeightedTorusDensity]
      ring
    _ = 0 := hz
end Ehrhart.WeightedTorusBochner
