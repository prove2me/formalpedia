-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation.momentTorusEnvelopeTimeSlice_le_holomorphicJointMollification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/80b299c5-a835-400c-9632-e433c622537b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicApproximation_momentWeakJointCoverUpperEnvelope_le_trueRadialMollification
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhysicalApproximation_momentWeakJointCoverUpperEnvelope_timeEmbedding_of_pos

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
    (p : LogSpace n) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (q : LogTorus n) :
    momentTorusEnvelopeTimeSlice K F htransport p q t ≤
      momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k
          (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t) := by
  rw [momentTorusEnvelopeTimeSlice,
    ← momentWeakJointCoverUpperEnvelope_timeEmbedding_of_pos
      K F htransport p (sourceTorusCoverPoint q) ht]
  exact momentWeakJointCoverUpperEnvelope_le_trueRadialMollification
    K F htransport p k
      (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t)
end Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation
