-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.partitioned_coverWeighted_integral_eq_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/2b90a71c-b487-404d-aec0-85a10b8025e6

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_integral_coverWeightedMeasure
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_integral_logarithmicCoordinates_eq_jacobian
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_integral_partitionedRealCoverIntegrand_eq_unweightedSourceTorus
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_integral_unweightedSourceTorusIntegrand_eq_weighted

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
    logarithmicCoverJacobianFactor n •
      (∫ z : TorusCharacters.LogSpace n,
        (coverAngularSmoothPartition z : ℂ) *
          f (complexTorusCoverProjection n z)
        ∂(coverWeightedMeasure (matrixSourceCoverPotential φ))) =
      ∫ p : WeightedTorusHilbert.LogTorus n,
        f p ∂(weightedTorusMeasure 1 φ) := by
  let g : TorusCharacters.LogSpace n → ℂ :=
    fun z =>
      complexCoverWeight (matrixSourceCoverPotential φ) z *
        ((coverAngularSmoothPartition z : ℂ) *
          f (complexTorusCoverProjection n z))
  have hcover := integral_coverWeightedMeasure
    (continuous_matrixSourceCoverPotential hφ)
    (fun z : TorusCharacters.LogSpace n =>
      (coverAngularSmoothPartition z : ℂ) *
        f (complexTorusCoverProjection n z))
  calc
    _ = logarithmicCoverJacobianFactor n •
      (∫ z : TorusCharacters.LogSpace n, g z
        ∂(volume : Measure (TorusCharacters.LogSpace n))) := by
      exact congrArg
        (fun q : ℂ => logarithmicCoverJacobianFactor n • q) hcover
    _ = ∫ p : Space n × Space n,
      g (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        p.1 p.2)
      ∂(volume : Measure (Space n × Space n)) :=
      (integral_logarithmicCoordinates_eq_jacobian g).symm
    _ = ∫ p : Space n × Space n,
      partitionedRealCoverIntegrand φ f p
      ∂(volume : Measure (Space n × Space n)) := by
      apply integral_congr_ae
      filter_upwards [] with p
      simp [g, complexCoverWeight, coverWeight,
        partitionedRealCoverIntegrand, realTorusCoverProjection]
    _ = ∫ p : WeightedTorusHilbert.LogTorus n,
      unweightedSourceTorusIntegrand φ f p
      ∂((volume : Measure (Space n)).prod
        (angularMeasure n)) :=
      integral_partitionedRealCoverIntegrand_eq_unweightedSourceTorus
        hφ hf hfc
    _ = _ := integral_unweightedSourceTorusIntegrand_eq_weighted hφ f
end Ehrhart.MatrixTorusBochnerBridge
