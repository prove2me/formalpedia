-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.integral_sourceCoverAngularPartitionDerivative_mul_lift_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/1c008d4f-025c-4068-b043-6b458ca83a73

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_integral_coverWeightedMeasure
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_integral_logarithmicCoordinates_eq_jacobian
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_integral_derivativePartitionedRealCoverIntegrand_eq_zero

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
    (∫ z : TorusCharacters.LogSpace n,
      (((fderiv ℝ (angularSmoothPartition (n := n))
        ((logarithmicCoordinatesEquiv n).symm z).2) v : ℂ) *
        f (complexTorusCoverProjection n z))
      ∂(coverWeightedMeasure (matrixSourceCoverPotential φ))) = 0 := by
  let F : TorusCharacters.LogSpace n → ℂ :=
    fun z =>
      (((fderiv ℝ (angularSmoothPartition (n := n))
        ((logarithmicCoordinatesEquiv n).symm z).2) v : ℂ) *
        f (complexTorusCoverProjection n z))
  let G : TorusCharacters.LogSpace n → ℂ :=
    fun z => complexCoverWeight (matrixSourceCoverPotential φ) z * F z
  have hcover := integral_coverWeightedMeasure
    (continuous_matrixSourceCoverPotential hφ) F
  have hsmul :
      logarithmicCoverJacobianFactor n •
        (∫ z : TorusCharacters.LogSpace n,
          F z ∂(coverWeightedMeasure (matrixSourceCoverPotential φ))) =
        0 := by
    calc
      _ = logarithmicCoverJacobianFactor n •
        (∫ z : TorusCharacters.LogSpace n,
          G z ∂(volume : Measure
            (TorusCharacters.LogSpace n))) := by
        exact congrArg
          (fun w : ℂ => logarithmicCoverJacobianFactor n • w)
          hcover
      _ = ∫ p : Space n × Space n,
        G (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
          p.1 p.2)
        ∂(volume : Measure (Space n × Space n)) :=
        (integral_logarithmicCoordinates_eq_jacobian G).symm
      _ = ∫ p : Space n × Space n,
        derivativePartitionedRealCoverIntegrand φ f v p
        ∂(volume : Measure (Space n × Space n)) := by
        apply integral_congr_ae
        filter_upwards [] with p
        simp only [G, F, complexCoverWeight, coverWeight,
          derivativePartitionedRealCoverIntegrand,
          matrixSourceCoverPotential,
          complexTorusCoverProjection,
          realTorusCoverProjection,
          ← logarithmicCoordinatesEquiv_apply,
          ContinuousLinearEquiv.symm_apply_apply]
      _ = 0 :=
        integral_derivativePartitionedRealCoverIntegrand_eq_zero
          hφ hf hfc v
  exact (smul_eq_zero.mp hsmul).resolve_left
    (logarithmicCoverJacobianFactor_pos n).ne'
end Ehrhart.MatrixTorusBochnerIdentity
