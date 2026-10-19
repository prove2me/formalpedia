-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.hasDerivAt_sourceFreeLogSlope_of_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/a215cd0a-2277-48fd-be41-03fa1b047feb

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_hasDerivAt_sourceFreePartition_of_majorant
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_hasDerivAt_sourceFreeFirstMoment_of_majorant

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
    (hjbound : ∀ u ∈ s, ∀ q : LogTorus n, |j u q| ≤ J)
    (hpart : 0 < sourcePartition a t) :
    HasDerivAt (sourceLogSlope a f)
      (sourceAccelerationMoment a j t / sourcePartition a t -
        sourceMomentVariance a f t) t := by
  have hp := hasDerivAt_sourceFreePartition_of_majorant
    a f hs ha hf hderiv M hM hdom hbound
  have hm := hasDerivAt_sourceFreeFirstMoment_of_majorant
    a f j hs ha hf hj hderiv hfderiv M hM hdom hbound hjbound
  change HasDerivAt
    (fun u : ℝ => sourceFirstMoment a f u / sourcePartition a u)
    (sourceAccelerationMoment a j t / sourcePartition a t -
      (sourceSecondMoment a f t / sourcePartition a t -
        (sourceFirstMoment a f t / sourcePartition a t) ^ 2)) t
  refine (hm.fun_div hp hpart.ne').congr_deriv ?_
  field_simp [hpart.ne']
  ring
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
