-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.hasDerivAt_sourceFreeFirstMoment_of_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/56dfc55c-9448-4924-828d-a6dfcfe22bb2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_sourceFreeWeightedObservable_integrable_of_majorant

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative LogPartitionConvexity
open JointHolomorphicLaurentFourierCompatibility EnvelopeSmoothing EnvelopeGeneralTorusDescent
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerIdentity MatrixTorusBochnerCoreApproximation WeightedTorusDolbeault
open WeightedTorusBrascampLieb MatrixTorusDolbeaultGraph RadialSchurBlock TorusDeckGraphAdjoint
open RadialPhysicalInverseSquareRootEnergy MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetJointHolomorphicStrictSchur BergmanJetJointHolomorphicFullLeviSchur
open BergmanJetHolomorphicPhysicalMeasure BergmanJetHolomorphicPhysicalSupport
open BergmanJetJointHolomorphicPhysicalApproximation BergmanJetJointHolomorphicTimeDerivativeBounds
open TorusHomogeneousBrascampLieb
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  MatrixOrder InnerProductSpace Topology ContDiff
namespace Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
theorem _root_.solution
    {n : ℕ}
    (a f j : ℝ → LogTorus n → ℝ)
    {t : ℝ} {s : Set ℝ} {B J : ℝ}
    (hs : s ∈ 𝓝 t)
    (ha : ∀ u : ℝ, Continuous (a u))
    (hf : ∀ u : ℝ, Continuous (f u))
    (hj : ∀ u : ℝ, Continuous (j u))
    (hderiv : ∀ (u : ℝ) (q : LogTorus n),
      HasDerivAt (fun v : ℝ => a v q) (f u q) u)
    (hfderiv : ∀ (u : ℝ) (q : LogTorus n),
      HasDerivAt (fun v : ℝ => f v q) (j u q) u)
    (M : LogTorus n → ℝ)
    (hM : Integrable M (sourceTorusBaseMeasure n))
    (hdom : ∀ u ∈ s, ∀ q : LogTorus n,
      sourceTimeDensity a u q ≤ M q)
    (hbound : ∀ u ∈ s, ∀ q : LogTorus n, |f u q| ≤ B)
    (hjbound : ∀ u ∈ s, ∀ q : LogTorus n, |j u q| ≤ J) :
    HasDerivAt (sourceFirstMoment a f)
      (sourceAccelerationMoment a j t - sourceSecondMoment a f t) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  have hmajor :
      Integrable
        (fun q : LogTorus n => (|J| + |B| ^ 2) * ‖M q‖)
        (sourceTorusBaseMeasure n) :=
    hM.norm.const_mul (|J| + |B| ^ 2)
  have hmeas :
      ∀ᶠ u in 𝓝 t,
        AEStronglyMeasurable
          (fun q : LogTorus n =>
            f u q * sourceTimeDensity a u q)
          (sourceTorusBaseMeasure n) :=
    Filter.Eventually.of_forall fun u =>
      ((hf u).mul
        (Real.continuous_exp.comp (ha u).neg)).aestronglyMeasurable
  have hdiffmeas : AEStronglyMeasurable
      (fun q : LogTorus n =>
        (j t q - f t q ^ 2) * sourceTimeDensity a t q)
      (sourceTorusBaseMeasure n) :=
    (((hj t).sub ((hf t).pow 2)).mul
      (Real.continuous_exp.comp (ha t).neg)).aestronglyMeasurable
  have hdom' :
      ∀ᵐ q ∂(sourceTorusBaseMeasure n),
        ∀ u ∈ s,
          ‖(j u q - f u q ^ 2) * sourceTimeDensity a u q‖ ≤
            (|J| + |B| ^ 2) * ‖M q‖ := by
    filter_upwards [] with q u hu
    have hfabs : |f u q| ≤ |B| :=
      (hbound u hu q).trans (le_abs_self B)
    have hjabs : |j u q| ≤ |J| :=
      (hjbound u hu q).trans (le_abs_self J)
    have hcoef : |j u q - f u q ^ 2| ≤ |J| + |B| ^ 2 := by
      calc
        |j u q - f u q ^ 2| ≤ |j u q| + |f u q ^ 2| :=
          abs_sub _ _
        _ = |j u q| + |f u q| ^ 2 := by rw [abs_pow]
        _ ≤ |J| + |B| ^ 2 :=
          add_le_add hjabs (pow_le_pow_left₀ (abs_nonneg _) hfabs 2)
    change
      |(j u q - f u q ^ 2) * Real.exp (-a u q)| ≤
        (|J| + |B| ^ 2) * ‖M q‖
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul hcoef
      ((hdom u hu q).trans (le_abs_self _))
      (Real.exp_pos _).le (by positivity)
  have hdiff :
      ∀ᵐ q ∂(sourceTorusBaseMeasure n),
        ∀ u ∈ s,
          HasDerivAt
            (fun v : ℝ => f v q * sourceTimeDensity a v q)
            ((j u q - f u q ^ 2) * sourceTimeDensity a u q) u := by
    filter_upwards [] with q u _
    have hprod := (hfderiv u q).fun_mul (hderiv u q).neg.exp
    refine (hprod.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    dsimp [sourceTimeDensity]
    ring
  have hfirstint := sourceFreeWeightedObservable_integrable_of_majorant
    a (f t) t B (ha t) (hf t) M hM (hdom t ht) (hbound t ht)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := sourceTorusBaseMeasure n)
    (F := fun u q => f u q * sourceTimeDensity a u q)
    (F' := fun u q =>
      (j u q - f u q ^ 2) * sourceTimeDensity a u q)
    (bound := fun q => (|J| + |B| ^ 2) * ‖M q‖)
    hs hmeas hfirstint hdiffmeas hdom' hmajor hdiff
  have hjint := sourceFreeWeightedObservable_integrable_of_majorant
    a (j t) t J (ha t) (hj t) M hM (hdom t ht) (hjbound t ht)
  have hsquare : ∀ q : LogTorus n, |f t q ^ 2| ≤ |B| ^ 2 := by
    intro q
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      ((hbound t ht q).trans (le_abs_self B)) 2
  have hsquareint := sourceFreeWeightedObservable_integrable_of_majorant
    a (fun q => f t q ^ 2) t (|B| ^ 2)
    (ha t) ((hf t).pow 2) M hM (hdom t ht) hsquare
  have hmoment :
      (∫ q : LogTorus n,
        (j t q - f t q ^ 2) * sourceTimeDensity a t q
          ∂(sourceTorusBaseMeasure n)) =
        sourceAccelerationMoment a j t - sourceSecondMoment a f t := by
    calc
      (∫ q : LogTorus n,
        (j t q - f t q ^ 2) * sourceTimeDensity a t q
          ∂(sourceTorusBaseMeasure n)) =
        ∫ q : LogTorus n,
          (j t q * sourceTimeDensity a t q -
            f t q ^ 2 * sourceTimeDensity a t q)
              ∂(sourceTorusBaseMeasure n) := by
                apply integral_congr_ae
                filter_upwards [] with q
                ring
      _ = sourceAccelerationMoment a j t - sourceSecondMoment a f t := by
        rw [integral_sub hjint hsquareint]
        rfl
  change HasDerivAt
    (fun u : ℝ =>
      ∫ q : LogTorus n,
        f u q * sourceTimeDensity a u q
          ∂(sourceTorusBaseMeasure n))
    (sourceAccelerationMoment a j t - sourceSecondMoment a f t) t
  rw [← hmoment]
  exact h.2
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
