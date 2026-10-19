-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation.tendsto_momentWeakHolomorphicStrictJointTimeDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/72d27e16-9133-4149-bb10-39269f5c94fc

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhysicalApproximation_tendsto_momentWeakHolomorphicStrictJointTorusWeight

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
        sourceTimeDensity
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p (ε k) k) t q)
      atTop
      (𝓝 (sourceTimeDensity
        (fun (u : ℝ) (w : LogTorus n) =>
          momentTorusEnvelopeTimeSlice K F htransport p w u)
        t q)) := by
  have hweight :=
    tendsto_momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε hε ht q
  change Tendsto
    (fun k : ℕ =>
      Real.exp
        (-momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p (ε k) k t q))
    atTop
    (𝓝 (Real.exp
      (-momentTorusEnvelopeTimeSlice
        K F htransport p q t)))
  have h := Real.continuous_exp.continuousAt.tendsto.comp hweight.neg
  refine h.congr' (Filter.Eventually.of_forall fun k => ?_)
  rfl
end Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation
