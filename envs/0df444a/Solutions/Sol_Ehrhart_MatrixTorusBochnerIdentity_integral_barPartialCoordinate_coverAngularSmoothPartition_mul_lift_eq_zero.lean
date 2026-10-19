-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.integral_barPartialCoordinate_coverAngularSmoothPartition_mul_lift_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/b6863eee-ccc5-4984-8380-12c6aabeb551

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_contDiff_coverAngularSmoothPartition
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_integral_fderiv_coverAngularSmoothPartition_mul_lift_eq_zero
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_integrable_sourceAngularDerivativeLift

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
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      barPartialCoordinate
        (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
        f (complexTorusCoverProjection n z)
      ∂(coverWeightedMeasure (matrixSourceCoverPotential φ))) = 0 := by
  let μ : Measure (TorusCharacters.LogSpace n) :=
    coverWeightedMeasure (matrixSourceCoverPotential φ)
  let v₀ : TorusCharacters.LogSpace n :=
    Pi.single j (1 : ℂ)
  let v₁ : TorusCharacters.LogSpace n :=
    Pi.single j Complex.I
  let d₀ := sourceAngularDerivativeLift f v₀
  let d₁ := sourceAngularDerivativeLift f v₁
  have hi₀ : Integrable d₀ μ :=
    integrable_sourceAngularDerivativeLift hφ hf hfc v₀
  have hi₁ : Integrable d₁ μ :=
    integrable_sourceAngularDerivativeLift hφ hf hfc v₁
  have hz₀ : (∫ z, d₀ z ∂μ) = 0 :=
    integral_fderiv_coverAngularSmoothPartition_mul_lift_eq_zero
      hφ hf hfc v₀
  have hz₁ : (∫ z, d₁ z ∂μ) = 0 :=
    integral_fderiv_coverAngularSmoothPartition_mul_lift_eq_zero
      hφ hf hfc v₁
  have hI :
      (∫ z, Complex.I * d₁ z ∂μ) =
        Complex.I * (∫ z, d₁ z ∂μ) :=
    MeasureTheory.integral_const_mul Complex.I d₁
  have hη : Differentiable ℝ
      (coverAngularSmoothPartition (n := n)) :=
    (contDiff_coverAngularSmoothPartition
      (n := n) (m := 1)).differentiable (by simp)
  change
    (∫ z : TorusCharacters.LogSpace n,
      barPartialCoordinate
        (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
        f (complexTorusCoverProjection n z) ∂μ) = 0
  calc
    _ = ∫ z : TorusCharacters.LogSpace n,
      (d₀ z + Complex.I * d₁ z) / 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      unfold barPartialCoordinate
      rw [DolbeaultGraphDistributionBridge.fderiv_complexOfReal
        hη z v₀,
        DolbeaultGraphDistributionBridge.fderiv_complexOfReal
          hη z v₁]
      change
        (((fderiv ℝ (coverAngularSmoothPartition (n := n)) z)
          v₀ : ℂ) +
          Complex.I *
            ((fderiv ℝ (coverAngularSmoothPartition (n := n)) z)
              v₁ : ℂ)) / 2 *
            f (complexTorusCoverProjection n z) =
          (d₀ z + Complex.I * d₁ z) / 2
      dsimp [d₀, d₁, sourceAngularDerivativeLift]
      ring
    _ = ((∫ z, d₀ z ∂μ) +
      Complex.I * (∫ z, d₁ z ∂μ)) / 2 := by
      rw [MeasureTheory.integral_div,
        MeasureTheory.integral_add hi₀ (hi₁.const_mul Complex.I),
        hI]
    _ = 0 := by rw [hz₀, hz₁]; norm_num
end Ehrhart.MatrixTorusBochnerIdentity
