-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation.momentWeakJointCoverUpperEnvelope_timeEmbedding_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/df4ffa86-105b-4812-9f36-4980c564a529

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicClosure_momentWeakJointCoverEnvelope_eq_upperEnvelope_of_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert MatrixTorusBochnerBridge MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentMoserTrudinger BergmanJetTorusEnvelope
open BergmanJetTorusCoercivity BergmanJetStrictRadialRegularizer
open BergmanJetJointEnvelopeRegularization BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetJointHolomorphicStrictSchur
open BergmanJetJointHolomorphicApproximation BergmanJetHolomorphicPhysicalMeasure
open JetEnvelopeRightDerivative JetEnvelopeSlopeConvergence JetEnvelopeGlobalPlurisubharmonic
open EnvelopeSmoothing EnvelopeGeneralTorusDescent LogPartitionConvexity
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder
namespace Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) {t : ℝ} (ht : 0 < t) :
    momentWeakJointCoverUpperEnvelope K F htransport p
      (sourceJointTimeEmbedding z t) =
        momentEnvelopeTimeSlice K F htransport p z t := by
  have htime :
      0 < sourceJointCoverTime (sourceJointTimeEmbedding z t) := by
    simpa [sourceJointCoverTime_timeEmbedding] using ht
  calc
    momentWeakJointCoverUpperEnvelope K F htransport p
        (sourceJointTimeEmbedding z t) =
      momentWeakJointCoverEnvelope K F htransport p
        (sourceJointTimeEmbedding z t) :=
      (momentWeakJointCoverEnvelope_eq_upperEnvelope_of_pos
        K F htransport p (sourceJointTimeEmbedding z t) htime).symm
    _ = momentEnvelopeTimeSlice K F htransport p z t := by
      unfold momentWeakJointCoverEnvelope
      rw [sourceJointCoverTime_timeEmbedding]
      rfl
end Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation
