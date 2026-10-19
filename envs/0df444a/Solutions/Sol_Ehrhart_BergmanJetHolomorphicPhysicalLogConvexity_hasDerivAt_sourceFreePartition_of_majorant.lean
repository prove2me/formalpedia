-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.hasDerivAt_sourceFreePartition_of_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/c4841842-c8ef-4652-a90c-2b033a389848

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_sourceFreeTimeDensity_integrable_of_majorant

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
    (a f : ℝ → LogTorus n → ℝ)
    {t : ℝ} {s : Set ℝ} {B : ℝ}
    (hs : s ∈ 𝓝 t)
    (ha : ∀ u : ℝ, Continuous (a u))
    (hf : ∀ u : ℝ, Continuous (f u))
    (hderiv : ∀ (u : ℝ) (q : LogTorus n),
      HasDerivAt (fun v : ℝ => a v q) (f u q) u)
    (M : LogTorus n → ℝ)
    (hM : Integrable M (sourceTorusBaseMeasure n))
    (hdom : ∀ u ∈ s, ∀ q : LogTorus n,
      sourceTimeDensity a u q ≤ M q)
    (hbound : ∀ u ∈ s, ∀ q : LogTorus n, |f u q| ≤ B) :
    HasDerivAt (sourcePartition a)
      (-sourceFirstMoment a f t) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  have hmajor :
      Integrable (fun q : LogTorus n => |B| * ‖M q‖)
        (sourceTorusBaseMeasure n) := by
    exact hM.norm.const_mul |B|
  have hmeas :
      ∀ᶠ u in 𝓝 t,
        AEStronglyMeasurable
          (sourceTimeDensity a u) (sourceTorusBaseMeasure n) :=
    Filter.Eventually.of_forall fun u =>
      (Real.continuous_exp.comp (ha u).neg).aestronglyMeasurable
  have hdiffmeas : AEStronglyMeasurable
      (fun q : LogTorus n =>
        -f t q * sourceTimeDensity a t q)
      (sourceTorusBaseMeasure n) :=
    ((hf t).neg.mul
      (Real.continuous_exp.comp (ha t).neg)).aestronglyMeasurable
  have hdom' :
      ∀ᵐ q ∂(sourceTorusBaseMeasure n),
        ∀ u ∈ s,
          ‖-f u q * sourceTimeDensity a u q‖ ≤
            |B| * ‖M q‖ := by
    filter_upwards [] with q u hu
    change |-f u q * Real.exp (-a u q)| ≤ |B| * ‖M q‖
    rw [abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul
      ((hbound u hu q).trans (le_abs_self B))
      ((hdom u hu q).trans (le_abs_self _))
      (Real.exp_pos _).le (abs_nonneg _)
  have hdiff :
      ∀ᵐ q ∂(sourceTorusBaseMeasure n),
        ∀ u ∈ s,
          HasDerivAt
            (fun v : ℝ => sourceTimeDensity a v q)
            (-f u q * sourceTimeDensity a u q) u := by
    filter_upwards [] with q u _
    simpa [sourceTimeDensity, mul_comm] using
      (hderiv u q).neg.exp
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := sourceTorusBaseMeasure n)
    (F := fun u q => sourceTimeDensity a u q)
    (F' := fun u q => -f u q * sourceTimeDensity a u q)
    (bound := fun q => |B| * ‖M q‖)
    hs hmeas
    (sourceFreeTimeDensity_integrable_of_majorant
      a t (ha t) M hM (hdom t ht))
    hdiffmeas hdom' hmajor hdiff
  have hmoment :
      (∫ q : LogTorus n,
        -f t q * sourceTimeDensity a t q
          ∂(sourceTorusBaseMeasure n)) =
        -sourceFirstMoment a f t := by
    calc
      (∫ q : LogTorus n,
        -f t q * sourceTimeDensity a t q
          ∂(sourceTorusBaseMeasure n)) =
        ∫ q : LogTorus n,
          -(f t q * sourceTimeDensity a t q)
            ∂(sourceTorusBaseMeasure n) := by
              apply integral_congr_ae
              filter_upwards [] with q
              ring
      _ = -sourceFirstMoment a f t := by
        rw [integral_neg]
        rfl
  change HasDerivAt
    (fun u : ℝ =>
      ∫ q : LogTorus n,
        sourceTimeDensity a u q ∂(sourceTorusBaseMeasure n))
    (-sourceFirstMoment a f t) t
  rw [← hmoment]
  exact h.2
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
