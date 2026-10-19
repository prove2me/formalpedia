-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.integral_derivativePartitionedRealCoverIntegrand_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/8aab0908-623c-476d-a462-cec33079e0b0

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_integral_fderiv_angularSmoothPartition_periodic_eq_zero
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_angularCoverProjection_binary_translate
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_integrable_derivativePartitionedRealCoverIntegrand

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
    (∫ p : Space n × Space n,
      derivativePartitionedRealCoverIntegrand φ f v p
      ∂(volume : Measure (Space n × Space n))) = 0 := by
  have hreal :=
    integrable_derivativePartitionedRealCoverIntegrand hφ hf hfc v
  have hrealprod :
      Integrable (derivativePartitionedRealCoverIntegrand φ f v)
        ((volume : Measure (Space n)).prod
          (volume : Measure (Space n))) := by
    rw [← Measure.volume_eq_prod]
    exact hreal
  calc
    _ = ∫ x : Space n,
      ∫ t : Space n,
        derivativePartitionedRealCoverIntegrand φ f v (x, t)
        ∂(volume : Measure (Space n))
        ∂(volume : Measure (Space n)) := by
      rw [Measure.volume_eq_prod]
      exact MeasureTheory.integral_prod _ hrealprod
    _ = ∫ _x : Space n, (0 : ℂ)
        ∂(volume : Measure (Space n)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      let g : Space n → ℂ :=
        fun t => f (x, angularCoverProjection n t)
      have hg : Continuous g :=
        hf.comp (continuous_const.prodMk
          (continuous_angularCoverProjection n))
      have hperiod : ∀ (q : Fin n → Bool) (t : Space n),
          g (binaryAngularFundamentalBase q + t) = g t := by
        intro q t
        change
          f (x, angularCoverProjection n
            (binaryAngularFundamentalBase q + t)) =
          f (x, angularCoverProjection n t)
        rw [angularCoverProjection_binary_translate]
      let d : Space n → ℂ :=
        fun t => ((fderiv ℝ
          (angularSmoothPartition (n := n)) t) v : ℂ)
      have hzero :
          (∫ t : Space n, d t * g t
            ∂(volume : Measure (Space n))) = 0 := by
        exact integral_fderiv_angularSmoothPartition_periodic_eq_zero
          v hg hperiod
      have hmul :
          (∫ t : Space n,
            (Real.exp (-φ x) : ℂ) * (d t * g t)
            ∂(volume : Measure (Space n))) =
          (Real.exp (-φ x) : ℂ) *
            (∫ t : Space n, d t * g t
              ∂(volume : Measure (Space n))) :=
        MeasureTheory.integral_const_mul
          (Real.exp (-φ x) : ℂ)
          (fun t : Space n => d t * g t)
      change
        (∫ t : Space n,
          (Real.exp (-φ x) : ℂ) * (d t * g t)
          ∂(volume : Measure (Space n))) = 0
      rw [hmul, hzero, mul_zero]
    _ = 0 := by simp
end Ehrhart.MatrixTorusBochnerIdentity
