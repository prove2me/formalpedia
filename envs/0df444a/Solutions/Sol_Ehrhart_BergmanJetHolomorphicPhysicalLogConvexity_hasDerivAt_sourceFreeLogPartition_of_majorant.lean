-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.hasDerivAt_sourceFreeLogPartition_of_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/de874465-cb80-404c-8f92-9cb839f62344

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_hasDerivAt_sourceFreePartition_of_majorant

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
    (hbound : ∀ u ∈ s, ∀ q : LogTorus n, |f u q| ≤ B)
    (hpart : 0 < sourcePartition a t) :
    HasDerivAt (sourceLogPartition a)
      (sourceLogSlope a f t) t := by
  have hfirst := hasDerivAt_sourceFreePartition_of_majorant
    a f hs ha hf hderiv M hM hdom hbound
  change HasDerivAt
    (fun u : ℝ => -Real.log (sourcePartition a u))
    (sourceFirstMoment a f t / sourcePartition a t) t
  have h := (hfirst.log hpart.ne').neg
  refine (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  ring
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
