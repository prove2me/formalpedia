-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.integral_fderiv_coverAngularSmoothPartition_mul_lift_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/161a85d3-ff12-4c46-9907-9f59a1d6276e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_integral_sourceCoverAngularPartitionDerivative_mul_lift_eq_zero
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_fderiv_coverAngularSmoothPartition_apply

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
    (v : TorusCharacters.LogSpace n) :
    (∫ z : TorusCharacters.LogSpace n,
      (((fderiv ℝ (coverAngularSmoothPartition (n := n)) z) v : ℂ) *
        f (complexTorusCoverProjection n z))
      ∂(coverWeightedMeasure (matrixSourceCoverPotential φ))) = 0 := by
  calc
    _ = ∫ z : TorusCharacters.LogSpace n,
      (((fderiv ℝ (angularSmoothPartition (n := n))
        ((logarithmicCoordinatesEquiv n).symm z).2)
          (((logarithmicCoordinatesEquiv n).symm v).2) : ℂ) *
        f (complexTorusCoverProjection n z))
      ∂(coverWeightedMeasure (matrixSourceCoverPotential φ)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [fderiv_coverAngularSmoothPartition_apply]
    _ = 0 :=
      integral_sourceCoverAngularPartitionDerivative_mul_lift_eq_zero
        hφ hf hfc (((logarithmicCoordinatesEquiv n).symm v).2)
end Ehrhart.MatrixTorusBochnerIdentity
