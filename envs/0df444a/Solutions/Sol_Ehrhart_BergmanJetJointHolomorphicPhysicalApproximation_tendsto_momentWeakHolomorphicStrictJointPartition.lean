-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation.tendsto_momentWeakHolomorphicStrictJointPartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/9b175f52-00ca-49ac-a0b0-874f9d9b8cc1

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhysicalApproximation_integrable_momentWeakHolomorphicUniformDensityMajorant
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhysicalApproximation_exp_neg_momentWeakHolomorphicStrictJointTorusWeight_le_uniform
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhysicalApproximation_tendsto_momentWeakHolomorphicStrictJointTimeDensity

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
        sourcePartition
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p (ε k) k) t)
      atTop
      (𝓝 (sourcePartition
        (fun (u : ℝ) (q : LogTorus n) =>
          momentTorusEnvelopeTimeSlice K F htransport p q u)
        t)) := by
  have hmajor :=
    integrable_momentWeakHolomorphicUniformDensityMajorant
      K F htransport
  have hdom :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := sourceTorusBaseMeasure n)
      (l := Filter.atTop)
      (F := fun (k : ℕ) (q : LogTorus n) =>
        sourceTimeDensity
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p (ε k) k) t q)
      (f := fun q : LogTorus n =>
        sourceTimeDensity
          (fun (u : ℝ) (w : LogTorus n) =>
            momentTorusEnvelopeTimeSlice K F htransport p w u)
          t q)
      (momentWeakHolomorphicUniformDensityMajorant
        K F htransport)
      (Filter.Eventually.of_forall fun k =>
        (Real.continuous_exp.comp
          (continuous_momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p (ε k) k t).neg).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun k =>
        Filter.Eventually.of_forall fun q => by
          change
            |Real.exp
              (-momentWeakHolomorphicStrictJointTorusWeight
                K F htransport p (ε k) k t q)| ≤
              momentWeakHolomorphicUniformDensityMajorant
                K F htransport q
          rw [abs_of_pos (Real.exp_pos _)]
          exact
            exp_neg_momentWeakHolomorphicStrictJointTorusWeight_le_uniform
              K F htransport p k ht (hε₀ k) (hε₁ k) q)
      hmajor
      (Filter.Eventually.of_forall fun q =>
        tendsto_momentWeakHolomorphicStrictJointTimeDensity
          K F htransport p ε hε ht q)
  simpa [sourcePartition] using hdom
end Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation
