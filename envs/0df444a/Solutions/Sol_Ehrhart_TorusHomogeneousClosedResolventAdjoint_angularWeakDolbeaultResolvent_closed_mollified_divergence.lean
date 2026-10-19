-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousClosedResolventAdjoint.angularWeakDolbeaultResolvent_closed_mollified_divergence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/c0c3320e-c96a-44ee-a9ce-ed10ca5b7fa2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultRegularity_translatedRealKernel_hasCompactSupport
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_compactSupport_barPartialCoordinate
import Theorems.Thm_Ehrhart_TorusWeightedDensityConvolutionDivergence_holomorphicCoordinate_normalizedCoverMollification_eq_kernel
import Theorems.Thm_Ehrhart_TorusWeightedDensityConvolutionDivergence_normalizedCoverMollification_eq_kernel_integral
import Theorems.Thm_Ehrhart_TorusHomogeneousClosedResolventAdjoint_angularWeakDolbeaultResolvent_unweighted_translated_bump_green

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
    (∑ j : Fin n,
      (holomorphicCoordinate
        (normalizedCoverMollification
          (complexTorusCoverLift
            (fun q : LogTorus n =>
              ((WithLp.snd
                (angularWeakDolbeaultResolvent a f :
                  angularDolbeaultGraphAmbient a)) q :
                EuclideanSpace ℂ (Fin n)) j)) k) x j -
      normalizedCoverMollification
        (fun y : LogSpace n =>
          holomorphicCoordinate
            (fun z : LogSpace n =>
              (angularCoverPotential a z : ℂ)) y j *
            complexTorusCoverLift
              (fun q : LogTorus n =>
                ((WithLp.snd
                  (angularWeakDolbeaultResolvent a f :
                    angularDolbeaultGraphAmbient a)) q :
                  EuclideanSpace ℂ (Fin n)) j) y) k x)) =
    -normalizedCoverMollification
      (complexTorusCoverLift
        (fun q : LogTorus n =>
          (f - angularWeakScalarResolventCLM a f) q)) k x := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  let η : LogSpace n → ℂ := fun y => (κ (x - y) : ℂ)
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a)
  let r : angularWeightedScalarL2 a :=
    f - angularWeakScalarResolventCLM a f
  let w : Fin n → LogSpace n → ℂ :=
    fun j y =>
      ((W (complexTorusCoverProjection n y) :
        EuclideanSpace ℂ (Fin n)) j)
  let b : Fin n → LogSpace n → ℂ :=
    fun j y => holomorphicCoordinate
      (fun z : LogSpace n =>
        (angularCoverPotential a z : ℂ)) y j
  have ha1 : ContDiff ℝ 1 (angularCoverPotential a) :=
    ha3.of_le (by norm_num)
  have hκ : ContDiff ℝ 1 κ :=
    (complexShrinkingBump (n := n) k).contDiff_normed
  have hη : ContDiff ℝ 1 η :=
    Complex.ofRealCLM.contDiff.comp
      (hκ.comp (contDiff_const.sub contDiff_id))
  have hκcompact :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
      (μ := (volume : Measure (LogSpace n)))
  have hηcompact : HasCompactSupport η := by
    simpa [η, Function.comp_def] using
      (translatedRealKernel_hasCompactSupport hκcompact x).comp_left
        (g := Complex.ofReal) (by simp)
  have hw (j : Fin n) :
      LocallyIntegrable (w j) (volume : Measure (LogSpace n)) := by
    exact angularWeightedFormCoordinateCoverLift_locallyIntegrable
      ha W j
  have hb (j : Fin n) : Continuous (b j) := by
    exact continuous_holomorphicCoordinate
      (Complex.ofRealCLM.contDiff.comp ha1) j
  have hbw (j : Fin n) :
      LocallyIntegrable (fun y : LogSpace n => b j y * w j y)
        (volume : Measure (LogSpace n)) :=
    locallyIntegrable_cover_complex_mul_continuous (hw j) (hb j)
  have hconjcont (j : Fin n) :
      Continuous (fun y : LogSpace n =>
        conj (barPartialCoordinate η y j)) :=
    Complex.continuous_conj.comp (continuous_barPartialCoordinate hη j)
  have hconjcompact (j : Fin n) :
      HasCompactSupport (fun y : LogSpace n =>
        conj (barPartialCoordinate η y j)) := by
    simpa [Function.comp_def] using
      (compactSupport_barPartialCoordinate hηcompact j).comp_left
        (g := (starRingEnd ℂ)) (map_zero _)
  have hi (j : Fin n) :
      Integrable
        (fun y : LogSpace n =>
          w j y * conj (barPartialCoordinate η y j))
        (volume : Measure (LogSpace n)) := by
    simpa [smul_eq_mul] using
      (hw j).integrable_smul_right_of_hasCompactSupport
        (hconjcont j) (hconjcompact j)
  have hbint (j : Fin n) :
      Integrable
        (fun y : LogSpace n =>
          (b j y * w j y) * η y)
        (volume : Measure (LogSpace n)) := by
    simpa [smul_eq_mul] using
      (hbw j).integrable_smul_right_of_hasCompactSupport
        hη.continuous hηcompact
  have hsplit (j : Fin n) :
      (∫ y : LogSpace n,
        w j y *
          (conj (barPartialCoordinate η y j) + η y * b j y)
        ∂(volume : Measure (LogSpace n))) =
      (∫ y : LogSpace n,
        w j y * conj (barPartialCoordinate η y j)
        ∂(volume : Measure (LogSpace n))) +
      (∫ y : LogSpace n,
        (b j y * w j y) * η y
        ∂(volume : Measure (LogSpace n))) := by
    rw [← integral_add (hi j) (hbint j)]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  have hwhole (j : Fin n) :
      Integrable
        (fun y : LogSpace n =>
          w j y *
            (conj (barPartialCoordinate η y j) + η y * b j y))
        (volume : Measure (LogSpace n)) := by
    have hs := (hi j).add (hbint j)
    apply hs.congr
    filter_upwards [] with y
    change
      w j y * conj (barPartialCoordinate η y j) +
          (b j y * w j y) * η y =
        w j y *
          (conj (barPartialCoordinate η y j) + η y * b j y)
    ring
  have hgreen :=
    angularWeakDolbeaultResolvent_unweighted_translated_bump_green
      ha ha3 f k x
  change
    (∫ y : LogSpace n,
      ∑ j : Fin n,
        w j y *
          (conj (barPartialCoordinate η y j) + η y * b j y)
      ∂(volume : Measure (LogSpace n))) =
    (∫ y : LogSpace n,
      r (complexTorusCoverProjection n y) * η y
      ∂(volume : Measure (LogSpace n))) at hgreen
  rw [integral_finsetSum Finset.univ
    (fun j _ => hwhole j)] at hgreen
  change
    (∑ j : Fin n,
      (holomorphicCoordinate
        (normalizedCoverMollification (w j) k) x j -
      normalizedCoverMollification
        (fun y : LogSpace n => b j y * w j y) k x)) =
      -normalizedCoverMollification
        (fun y : LogSpace n =>
          r (complexTorusCoverProjection n y)) k x
  calc
    _ = ∑ j : Fin n,
      (-(∫ y : LogSpace n,
          w j y * conj (barPartialCoordinate η y j)
          ∂(volume : Measure (LogSpace n))) -
       (∫ y : LogSpace n,
          (b j y * w j y) * η y
          ∂(volume : Measure (LogSpace n)))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [holomorphicCoordinate_normalizedCoverMollification_eq_kernel
        (hw j) k x j,
        normalizedCoverMollification_eq_kernel_integral
          (fun y : LogSpace n => b j y * w j y) k x]
    _ = -(∑ j : Fin n,
      ∫ y : LogSpace n,
        w j y *
          (conj (barPartialCoordinate η y j) + η y * b j y)
        ∂(volume : Measure (LogSpace n))) := by
      simp_rw [hsplit]
      simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        Finset.sum_add_distrib]
      ring
    _ = -(∫ y : LogSpace n,
      r (complexTorusCoverProjection n y) * η y
      ∂(volume : Measure (LogSpace n))) :=
      congrArg Neg.neg hgreen
    _ = _ := by
      rw [normalizedCoverMollification_eq_kernel_integral]
end Ehrhart.TorusHomogeneousClosedResolventAdjoint
