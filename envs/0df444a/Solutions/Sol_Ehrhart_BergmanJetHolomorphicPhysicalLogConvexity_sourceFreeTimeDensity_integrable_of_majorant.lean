-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.sourceFreeTimeDensity_integrable_of_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/05d8d62b-e16e-4bac-8dcf-f198b1d51031

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
    (a : ℝ → LogTorus n → ℝ) (t : ℝ)
    (ha : Continuous (a t))
    (M : LogTorus n → ℝ)
    (hM : Integrable M (sourceTorusBaseMeasure n))
    (hdom : ∀ q : LogTorus n, sourceTimeDensity a t q ≤ M q) :
    Integrable (sourceTimeDensity a t) (sourceTorusBaseMeasure n) := by
  apply hM.mono'
    ((Real.continuous_exp.comp ha.neg).aestronglyMeasurable)
  filter_upwards [] with q
  change |Real.exp (-a t q)| ≤ M q
  rw [abs_of_pos (Real.exp_pos _)]
  exact hdom q
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
