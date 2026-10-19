-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation.tendsto_momentWeakHolomorphicStrictJointCoverWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/45f86e65-09c6-456b-9741-612f84ca3b36

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicApproximation_tendsto_momentWeakHolomorphicJointTrueRadialMollification

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
    (q : SourceJointComplexCover n) :
    Tendsto
      (fun k : ℕ =>
        momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p (ε k) k q)
      atTop
      (𝓝 (momentWeakJointCoverUpperEnvelope
        K F htransport p q)) := by
  have hmoll :=
    tendsto_momentWeakHolomorphicJointTrueRadialMollification
      K F htransport p q
  have hone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have hreference :
      Tendsto
        (fun _ : ℕ =>
          matrixSourceCoverPotential
            (momentBodyStrictRadialPotential K) q.1)
        atTop
        (𝓝 (matrixSourceCoverPotential
          (momentBodyStrictRadialPotential K) q.1)) :=
    tendsto_const_nhds
  have hmix :=
    ((hone.sub hε).mul hmoll).add
      (hε.mul hreference)
  simpa [momentWeakHolomorphicStrictJointCoverWeight]
    using hmix
end Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation
