-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousClosedResolventAdjoint.angularWeakDolbeaultResolvent_unweighted_translated_bump_green
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/1f98c84d-222e-4c23-8a5a-4e9dd809f841

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_integral_coverWeightedMeasure
import Theorems.Thm_Ehrhart_WeightedTorusDolbeault_continuous_angularCoverPotential
import Theorems.Thm_Ehrhart_TorusClosedMollifierAdjoint_hasCompactSupport_translatedDensityCancelledCoverKernel
import Theorems.Thm_Ehrhart_TorusClosedMollifierAdjoint_complexCoverWeight_mul_translatedDensityCancelledCoverKernel
import Theorems.Thm_Ehrhart_TorusClosedMollifierAdjoint_complexCoverWeight_mul_conj_barPartial_translatedDensityCancelledCoverKernel
import Theorems.Thm_Ehrhart_TorusHomogeneousResolventGreen_angularWeakDolbeaultResolvent_weighted_cover_green
import Theorems.Thm_Ehrhart_TorusHomogeneousClosedResolventAdjoint_contDiff_translatedDensityCancelledCoverKernel_three

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousClosedResolventAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert DolbeaultRegularity
open WeightedTorusDistributionBridge WeightedDolbeaultBochnerIdentity WeightedTorusDolbeault
open WeightedTorusBrascampLieb TorusWeakDolbeaultMollification TorusFriedrichsMollifierEstimates
open TorusMollifiedBochner TorusWeightedAdjointMollification
open TorusWeightedDensityConvolutionDivergence TorusClosedMollifierAdjoint
open BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusHomogeneousClosedResolventAdjoint
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (f : angularWeightedScalarL2 a)
    (k : ℕ) (x : LogSpace n) :
    (∫ y : LogSpace n,
      ∑ j : Fin n,
        ((WithLp.snd
          (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a))
          (complexTorusCoverProjection n y) :
          EuclideanSpace ℂ (Fin n)) j *
        (conj (barPartialCoordinate
          (fun z : LogSpace n =>
            ((complexShrinkingBump (n := n) k).normed
              (volume : Measure (LogSpace n)) (x - z) : ℂ)) y j) +
          ((complexShrinkingBump (n := n) k).normed
            (volume : Measure (LogSpace n)) (x - y) : ℂ) *
            holomorphicCoordinate
              (fun z : LogSpace n =>
                (angularCoverPotential a z : ℂ)) y j)
      ∂(volume : Measure (LogSpace n))) =
    (∫ y : LogSpace n,
      ((f - angularWeakScalarResolventCLM a f)
        (complexTorusCoverProjection n y)) *
        ((complexShrinkingBump (n := n) k).normed
          (volume : Measure (LogSpace n)) (x - y) : ℂ)
      ∂(volume : Measure (LogSpace n))) := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  let χ : LogSpace n → ℝ :=
    translatedDensityCancelledCoverKernel a k x
  let ψ : LogSpace n → ℂ := fun y => (χ y : ℂ)
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a)
  let r : angularWeightedScalarL2 a :=
    f - angularWeakScalarResolventCLM a f
  let d : LogSpace n → ℂ :=
    complexCoverWeight (angularCoverPotential a)
  have ha1 : ContDiff ℝ 1 (angularCoverPotential a) :=
    ha3.of_le (by norm_num)
  have hχ : ContDiff ℝ 3 χ :=
    contDiff_translatedDensityCancelledCoverKernel_three ha3 k x
  have hψ : ContDiff ℝ 3 ψ :=
    Complex.ofRealCLM.contDiff.comp hχ
  have hψcompact : HasCompactSupport ψ := by
    have ht := hasCompactSupport_translatedDensityCancelledCoverKernel
      a k x
    simpa [ψ, Function.comp_def] using
      ht.comp_left (g := Complex.ofReal) (by simp)
  have hg :=
    TorusHomogeneousResolventGreen.angularWeakDolbeaultResolvent_weighted_cover_green
      ha f hψ hψcompact
  rw [integral_coverWeightedMeasure
        (continuous_angularCoverPotential ha),
      integral_coverWeightedMeasure
        (continuous_angularCoverPotential ha)] at hg
  change
    (∫ y : LogSpace n,
      d y *
        @inner ℂ (EuclideanSpace ℂ (Fin n)) _
          (W (complexTorusCoverProjection n y))
          (WithLp.toLp 2
            (fun j : Fin n => barPartialCoordinate ψ y j))
      ∂(volume : Measure (LogSpace n))) =
    (∫ y : LogSpace n,
      d y * @inner ℂ ℂ _
        (r (complexTorusCoverProjection n y)) (ψ y)
      ∂(volume : Measure (LogSpace n))) at hg
  have hconj :
      (∫ y : LogSpace n,
        ∑ j : Fin n,
          d y *
            ((W (complexTorusCoverProjection n y) :
              EuclideanSpace ℂ (Fin n)) j) *
            conj (barPartialCoordinate ψ y j)
        ∂(volume : Measure (LogSpace n))) =
      (∫ y : LogSpace n,
        d y * (r (complexTorusCoverProjection n y)) * ψ y
        ∂(volume : Measure (LogSpace n))) := by
    calc
      _ = conj
          (∫ y : LogSpace n,
            d y *
              @inner ℂ (EuclideanSpace ℂ (Fin n)) _
                (W (complexTorusCoverProjection n y))
                (WithLp.toLp 2
                  (fun j : Fin n => barPartialCoordinate ψ y j))
            ∂(volume : Measure (LogSpace n))) := by
        rw [← integral_conj]
        apply integral_congr_ae
        filter_upwards [] with y
        simp [PiLp.inner_apply, RCLike.inner_apply,
          d, complexCoverWeight, map_sum, map_mul,
          Finset.mul_sum, mul_assoc, mul_comm]
      _ = conj
          (∫ y : LogSpace n,
            d y * @inner ℂ ℂ _
              (r (complexTorusCoverProjection n y)) (ψ y)
            ∂(volume : Measure (LogSpace n))) :=
        congrArg (starRingEnd ℂ) hg
      _ = _ := by
        rw [← integral_conj]
        apply integral_congr_ae
        filter_upwards [] with y
        simp [RCLike.inner_apply, d, complexCoverWeight, ψ,
          map_mul, mul_comm, mul_left_comm]
  change
    (∫ y : LogSpace n,
      ∑ j : Fin n,
        ((W (complexTorusCoverProjection n y) :
          EuclideanSpace ℂ (Fin n)) j) *
          (conj (barPartialCoordinate
            (fun z : LogSpace n => (κ (x - z) : ℂ)) y j) +
            (κ (x - y) : ℂ) *
              holomorphicCoordinate
                (fun z : LogSpace n =>
                  (angularCoverPotential a z : ℂ)) y j)
      ∂(volume : Measure (LogSpace n))) =
    (∫ y : LogSpace n,
      (r (complexTorusCoverProjection n y)) * (κ (x - y) : ℂ)
      ∂(volume : Measure (LogSpace n)))
  calc
    _ = (∫ y : LogSpace n,
      ∑ j : Fin n,
        d y *
          ((W (complexTorusCoverProjection n y) :
            EuclideanSpace ℂ (Fin n)) j) *
          conj (barPartialCoordinate ψ y j)
      ∂(volume : Measure (LogSpace n))) := by
      apply integral_congr_ae
      filter_upwards [] with y
      apply Finset.sum_congr rfl
      intro j _
      have he :=
        complexCoverWeight_mul_conj_barPartial_translatedDensityCancelledCoverKernel
          ha1 k x y j
      change
        ((W (complexTorusCoverProjection n y) :
          EuclideanSpace ℂ (Fin n)) j) *
          (conj (barPartialCoordinate
            (fun z : LogSpace n => (κ (x - z) : ℂ)) y j) +
            (κ (x - y) : ℂ) *
              holomorphicCoordinate
                (fun z : LogSpace n =>
                  (angularCoverPotential a z : ℂ)) y j) =
        d y *
          ((W (complexTorusCoverProjection n y) :
            EuclideanSpace ℂ (Fin n)) j) *
          conj (barPartialCoordinate ψ y j)
      change
        ((W (complexTorusCoverProjection n y) :
          EuclideanSpace ℂ (Fin n)) j) *
          (conj (barPartialCoordinate
            (fun z : LogSpace n => (κ (x - z) : ℂ)) y j) +
            (κ (x - y) : ℂ) *
              holomorphicCoordinate
                (fun z : LogSpace n =>
                  (angularCoverPotential a z : ℂ)) y j) =
        complexCoverWeight (angularCoverPotential a) y *
          ((W (complexTorusCoverProjection n y) :
            EuclideanSpace ℂ (Fin n)) j) *
          conj (barPartialCoordinate
            (fun z : LogSpace n =>
              (translatedDensityCancelledCoverKernel a k x z : ℂ)) y j)
      rw [← he]
      ring
    _ = (∫ y : LogSpace n,
      d y * (r (complexTorusCoverProjection n y)) * ψ y
      ∂(volume : Measure (LogSpace n))) := hconj
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      have he := complexCoverWeight_mul_translatedDensityCancelledCoverKernel
        a k x y
      change
        complexCoverWeight (angularCoverPotential a) y *
          (r (complexTorusCoverProjection n y)) *
            (translatedDensityCancelledCoverKernel a k x y : ℂ) =
        (r (complexTorusCoverProjection n y)) * (κ (x - y) : ℂ)
      rw [mul_right_comm, he]
      simp [κ, mul_comm]
end Ehrhart.TorusHomogeneousClosedResolventAdjoint
