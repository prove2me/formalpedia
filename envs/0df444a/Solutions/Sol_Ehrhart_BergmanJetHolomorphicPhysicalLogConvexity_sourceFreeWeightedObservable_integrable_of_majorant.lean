-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.sourceFreeWeightedObservable_integrable_of_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/3848d5ed-b8dc-4cb5-8b10-d6d79f14f059

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    (a : ℝ → LogTorus n → ℝ)
    (F : LogTorus n → ℝ) (t B : ℝ)
    (ha : Continuous (a t)) (hF : Continuous F)
    (M : LogTorus n → ℝ)
    (hM : Integrable M (sourceTorusBaseMeasure n))
    (hdom : ∀ q : LogTorus n, sourceTimeDensity a t q ≤ M q)
    (hbound : ∀ q : LogTorus n, |F q| ≤ B) :
    Integrable (fun q => F q * sourceTimeDensity a t q)
      (sourceTorusBaseMeasure n) := by
  have hmajor := hM.norm.const_mul |B|
  apply hmajor.mono'
    ((hF.mul (Real.continuous_exp.comp ha.neg)).aestronglyMeasurable)
  filter_upwards [] with q
  change |F q * Real.exp (-a t q)| ≤
    |B| * ‖M q‖
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hnonneg : 0 ≤ M q :=
    (Real.exp_pos (-a t q)).le.trans (hdom q)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    |F q| * Real.exp (-a t q) ≤ |B| * M q :=
      mul_le_mul
        ((hbound q).trans (le_abs_self B))
        (hdom q) (Real.exp_pos _).le (abs_nonneg _)
    _ = |B| * M q := rfl
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
