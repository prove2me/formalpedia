-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation.tendsto_momentWeakHolomorphicStrictJointLogPartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/ed9688f1-5ca6-481e-8c9b-d789b8618935

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhysicalApproximation_tendsto_momentWeakHolomorphicStrictJointPartition

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
    (hε₀ : ∀ k : ℕ, 0 ≤ ε k)
    (hε₁ : ∀ k : ℕ, ε k ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun k : ℕ =>
        sourceLogPartition
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p (ε k) k) t)
      atTop
      (𝓝 (sourceLogPartition
        (fun (u : ℝ) (q : LogTorus n) =>
          momentTorusEnvelopeTimeSlice K F htransport p q u)
        t)) := by
  have hpart :=
    tendsto_momentWeakHolomorphicStrictJointPartition
      K F htransport p ε hε hε₀ hε₁ ht
  have hpos := momentTorusEnvelopePartition_pos
    K F htransport p t
  have hlog :=
    (Real.continuousAt_log hpos.ne').tendsto.comp hpart
  simpa [sourceLogPartition, sourcePartition, sourceTimeDensity]
    using hlog.neg
end Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation
