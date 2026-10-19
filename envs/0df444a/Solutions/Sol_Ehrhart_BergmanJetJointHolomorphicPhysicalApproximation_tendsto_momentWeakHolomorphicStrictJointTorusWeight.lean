-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation.tendsto_momentWeakHolomorphicStrictJointTorusWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/811d9f18-5f79-4a46-9018-8f17e0c12c30

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhysicalApproximation_momentWeakJointCoverUpperEnvelope_timeEmbedding_of_pos
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhysicalApproximation_tendsto_momentWeakHolomorphicStrictJointCoverWeight

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
    (p : LogSpace n) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 (0 : ℝ)))
    {t : ℝ} (ht : 0 < t) (q : LogTorus n) :
    Tendsto
      (fun k : ℕ =>
        momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p (ε k) k t q)
      atTop
      (𝓝 (momentTorusEnvelopeTimeSlice
        K F htransport p q t)) := by
  have hcover :=
    tendsto_momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε hε
        (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t)
  rw [momentWeakJointCoverUpperEnvelope_timeEmbedding_of_pos
    K F htransport p (sourceTorusCoverPoint q) ht] at hcover
  simpa [momentWeakHolomorphicStrictJointTorusWeight,
    jointSourceTorusWeight_eq_cover,
    momentTorusEnvelopeTimeSlice] using hcover
end Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation
