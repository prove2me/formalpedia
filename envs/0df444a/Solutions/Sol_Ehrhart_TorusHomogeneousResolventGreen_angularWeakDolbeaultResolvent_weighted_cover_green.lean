-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousResolventGreen.angularWeakDolbeaultResolvent_weighted_cover_green
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/e9835bd1-8343-4a8b-90aa-f87967dca242

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_integral_coverWeightedMeasure
import Theorems.Thm_Ehrhart_WeightedTorusDolbeault_continuous_angularCoverPotential
import Theorems.Thm_Ehrhart_TorusDeckWeightedUnfolding_exists_finite_complex_fundamental_test_partition
import Theorems.Thm_Ehrhart_TorusWeightedCoverAdjointGreen_angularWeakDolbeaultResolvent_weighted_cover_green_of_fundamentalInterior
import Theorems.Thm_Ehrhart_TorusWeightedCoverGlobalGreen_barPartialCoordinate_finset_sum_complex
import Theorems.Thm_Ehrhart_TorusHomogeneousResolventGreen_angularWeightedScalarCover_density_inner_integrable
import Theorems.Thm_Ehrhart_TorusHomogeneousResolventGreen_angularWeightedFormCover_density_inner_integrable

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousResolventGreen
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert
open WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge
open WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault WeightedTorusBrascampLieb
open TorusDeckWeightedUnfolding TorusWeightedCoverAdjointGreen TorusWeightedCoverGlobalGreen
open BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold
namespace Ehrhart.TorusHomogeneousResolventGreen
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (f : angularWeightedScalarL2 a)
    {ψ : LogSpace n → ℂ}
    (hψ : ContDiff ℝ 3 ψ) (hψcompact : HasCompactSupport ψ) :
    (∫ z : LogSpace n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        ((WithLp.snd
          (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a))
              (complexTorusCoverProjection n z))
        (WithLp.toLp 2
          (fun j : Fin n => barPartialCoordinate ψ z j))
      ∂(coverWeightedMeasure (angularCoverPotential a))) =
    (∫ z : LogSpace n,
      @inner ℂ ℂ _
        ((f - angularWeakScalarResolventCLM a f)
          (complexTorusCoverProjection n z))
        (ψ z)
      ∂(coverWeightedMeasure (angularCoverPotential a))) := by
  classical
  obtain ⟨s, χ, hχ, hχsupport, hpartition⟩ :=
    exists_finite_complex_fundamental_test_partition hψcompact
  let ξ : LogSpace n → LogSpace n → ℂ :=
    fun i z => (χ i z : ℂ) * ψ z
  have hξ : ∀ i, ContDiff ℝ 3 (ξ i) := by
    intro i
    exact (Complex.ofRealCLM.contDiff.comp
      ((hχ i).of_le
        (WithTop.coe_le_coe.mpr
          (show (3 : ℕ∞) ≤ ⊤ from le_top)))).mul hψ
  have hξcompact : ∀ i, HasCompactSupport (ξ i) := by
    intro i
    exact hψcompact.mul_left
  have hξcell : ∀ i,
      tsupport (ξ i) ⊆
        coverFundamentalInterior (coverCenteredFundamentalBase i) := by
    intro i
    change tsupport (fun z => (χ i z : ℂ) * ψ z) ⊆ _
    refine tsupport_mul_subset_left.trans ?_
    refine (closure_mono ?_).trans (hχsupport i)
    intro z hz
    change (χ i z : ℂ) ≠ 0 at hz
    change χ i z ≠ 0
    intro hzzero
    apply hz
    simp [hzzero]
  have hψsum : ψ = fun z => ∑ i ∈ s, ξ i z := by
    funext z
    exact hpartition z
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a)
  let r : angularWeightedScalarL2 a :=
    f - angularWeakScalarResolventCLM a f
  have hintW : ∀ i ∈ s, Integrable
      (fun z : LogSpace n =>
        complexCoverWeight (angularCoverPotential a) z *
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n z))
            (WithLp.toLp 2
              (fun j : Fin n => barPartialCoordinate (ξ i) z j)))
      (volume : Measure (LogSpace n)) := by
    intro i _
    exact angularWeightedFormCover_density_inner_integrable
      ha W ((hξ i).of_le (by norm_num)) (hξcompact i)
  have hintr : ∀ i ∈ s, Integrable
      (fun z : LogSpace n =>
        complexCoverWeight (angularCoverPotential a) z *
          @inner ℂ ℂ _
            (r (complexTorusCoverProjection n z)) (ξ i z))
      (volume : Measure (LogSpace n)) := by
    intro i _
    exact angularWeightedScalarCover_density_inner_integrable
      ha r (hξ i).continuous (hξcompact i)
  have hrow (z : LogSpace n) :
      WithLp.toLp 2 (fun j : Fin n => barPartialCoordinate ψ z j) =
        ∑ i ∈ s, WithLp.toLp 2
          (fun j : Fin n => barPartialCoordinate (ξ i) z j) := by
    ext j
    simpa [hψsum] using
      (barPartialCoordinate_finset_sum_complex s ξ
        (fun i _ => (hξ i).of_le (by norm_num)) j z)
  change
    (∫ z : LogSpace n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (W (complexTorusCoverProjection n z))
        (WithLp.toLp 2
          (fun j : Fin n => barPartialCoordinate ψ z j))
      ∂(coverWeightedMeasure (angularCoverPotential a))) =
    (∫ z : LogSpace n,
      @inner ℂ ℂ _
        (r (complexTorusCoverProjection n z)) (ψ z)
      ∂(coverWeightedMeasure (angularCoverPotential a)))
  rw [integral_coverWeightedMeasure
        (continuous_angularCoverPotential ha),
      integral_coverWeightedMeasure
        (continuous_angularCoverPotential ha)]
  calc
    (∫ z : LogSpace n,
      complexCoverWeight (angularCoverPotential a) z *
        @inner ℂ (EuclideanSpace ℂ (Fin n)) _
          (W (complexTorusCoverProjection n z))
          (WithLp.toLp 2
            (fun j : Fin n => barPartialCoordinate ψ z j))
      ∂(volume : Measure (LogSpace n))) =
      ∫ z : LogSpace n, ∑ i ∈ s,
        complexCoverWeight (angularCoverPotential a) z *
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n z))
            (WithLp.toLp 2
              (fun j : Fin n => barPartialCoordinate (ξ i) z j))
        ∂(volume : Measure (LogSpace n)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hrow z]
      rw [inner_sum]
      simp [Finset.mul_sum]
    _ = ∑ i ∈ s,
      ∫ z : LogSpace n,
        complexCoverWeight (angularCoverPotential a) z *
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n z))
            (WithLp.toLp 2
              (fun j : Fin n => barPartialCoordinate (ξ i) z j))
          ∂(volume : Measure (LogSpace n)) :=
      integral_finsetSum s hintW
    _ = ∑ i ∈ s,
      ∫ z : LogSpace n,
        complexCoverWeight (angularCoverPotential a) z *
          @inner ℂ ℂ _
            (r (complexTorusCoverProjection n z)) (ξ i z)
          ∂(volume : Measure (LogSpace n)) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi :=
        angularWeakDolbeaultResolvent_weighted_cover_green_of_fundamentalInterior
          ha (coverCenteredFundamentalBase i) f
          (hξ i) (hξcompact i) (hξcell i)
      change
        (∫ z : LogSpace n,
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n z))
            (WithLp.toLp 2
              (fun j : Fin n => barPartialCoordinate (ξ i) z j))
          ∂(coverWeightedMeasure (angularCoverPotential a))) =
        (∫ z : LogSpace n,
          @inner ℂ ℂ _
            (r (complexTorusCoverProjection n z)) (ξ i z)
          ∂(coverWeightedMeasure (angularCoverPotential a))) at hi
      rw [integral_coverWeightedMeasure
            (continuous_angularCoverPotential ha),
          integral_coverWeightedMeasure
            (continuous_angularCoverPotential ha)] at hi
      exact hi
    _ = ∫ z : LogSpace n, ∑ i ∈ s,
      complexCoverWeight (angularCoverPotential a) z *
        @inner ℂ ℂ _
          (r (complexTorusCoverProjection n z)) (ξ i z)
        ∂(volume : Measure (LogSpace n)) :=
      (integral_finsetSum s hintr).symm
    _ = ∫ z : LogSpace n,
      complexCoverWeight (angularCoverPotential a) z *
        @inner ℂ ℂ _
          (r (complexTorusCoverProjection n z)) (ψ z)
        ∂(volume : Measure (LogSpace n)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hψsum]
      simp [Finset.mul_sum, Finset.sum_mul]
end Ehrhart.TorusHomogeneousResolventGreen
