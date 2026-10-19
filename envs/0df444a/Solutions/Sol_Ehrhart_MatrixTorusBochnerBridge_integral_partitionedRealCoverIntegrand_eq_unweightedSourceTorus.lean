-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.integral_partitionedRealCoverIntegrand_eq_unweightedSourceTorus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/ab28a854-9f8b-4519-90fa-b455362aa66a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_integral_angularSmoothPartition_eq_angularHaar
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_integrable_partitionedRealCoverIntegrand
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_integrable_unweightedSourceTorusIntegrand

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
    (∫ p : Space n × Space n,
      partitionedRealCoverIntegrand φ f p
      ∂(volume : Measure (Space n × Space n))) =
    ∫ p : WeightedTorusHilbert.LogTorus n,
      unweightedSourceTorusIntegrand φ f p
      ∂((volume : Measure (Space n)).prod
        (angularMeasure n)) := by
  have hreal := integrable_partitionedRealCoverIntegrand hφ hf hfc
  have hrealprod :
      Integrable (partitionedRealCoverIntegrand φ f)
        ((volume : Measure (Space n)).prod
          (volume : Measure (Space n))) := by
    rw [← Measure.volume_eq_prod]
    exact hreal
  have htorus := integrable_unweightedSourceTorusIntegrand hφ hf hfc
  calc
    _ = ∫ x : Space n,
      ∫ t : Space n,
        partitionedRealCoverIntegrand φ f (x, t)
        ∂(volume : Measure (Space n))
        ∂(volume : Measure (Space n)) := by
      rw [Measure.volume_eq_prod]
      exact MeasureTheory.integral_prod _ hrealprod
    _ = ∫ x : Space n,
      ∫ θ : TorusCharacters.AngularTorus n,
        unweightedSourceTorusIntegrand φ f (x, θ)
        ∂(angularMeasure n)
        ∂(volume : Measure (Space n)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      have hg : Continuous
          (fun θ : TorusCharacters.AngularTorus n =>
            f (x, θ)) :=
        hf.comp (continuous_const.prodMk continuous_id)
      have hpartition :=
        integral_angularSmoothPartition_eq_angularHaar hg
      have hcovermul :
          (∫ t : Space n,
            (Real.exp (-φ x) : ℂ) *
              ((angularSmoothPartition t : ℂ) *
                f (x, angularCoverProjection n t))
            ∂(volume : Measure (Space n))) =
          (Real.exp (-φ x) : ℂ) *
            (∫ t : Space n,
              (angularSmoothPartition t : ℂ) *
                f (x, angularCoverProjection n t)
              ∂(volume : Measure (Space n))) :=
        MeasureTheory.integral_const_mul
          (Real.exp (-φ x) : ℂ)
          (fun t : Space n =>
            (angularSmoothPartition t : ℂ) *
              f (x, angularCoverProjection n t))
      have htorusmul :
          (∫ θ : TorusCharacters.AngularTorus n,
            (Real.exp (-φ x) : ℂ) * f (x, θ)
            ∂(angularMeasure n)) =
          (Real.exp (-φ x) : ℂ) *
            (∫ θ : TorusCharacters.AngularTorus n,
              f (x, θ) ∂(angularMeasure n)) :=
        MeasureTheory.integral_const_mul
          (Real.exp (-φ x) : ℂ)
          (fun θ : TorusCharacters.AngularTorus n => f (x, θ))
      change
        (∫ t : Space n,
          (Real.exp (-φ x) : ℂ) *
            ((angularSmoothPartition t : ℂ) *
              f (x, angularCoverProjection n t))
          ∂(volume : Measure (Space n))) =
        ∫ θ : TorusCharacters.AngularTorus n,
          (Real.exp (-φ x) : ℂ) * f (x, θ)
          ∂(angularMeasure n)
      rw [hcovermul, htorusmul, hpartition]
    _ = _ := (MeasureTheory.integral_prod _ htorus).symm
end Ehrhart.MatrixTorusBochnerBridge
