-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation.exp_neg_momentWeakHolomorphicStrictJointTorusWeight_le_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/e292f90d-c712-455c-9e76-5c88b687a7c9

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhysicalApproximation_momentWeakHolomorphicStrictJointTorusWeight_uniform_norm_coercivity

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
    {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (q : LogTorus n) :
    Real.exp
        (-momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t q) ≤
      momentWeakHolomorphicUniformDensityMajorant
        K F htransport q := by
  unfold momentWeakHolomorphicUniformDensityMajorant
  simp only [mul_one]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hcoerce :=
    momentWeakHolomorphicStrictJointTorusWeight_uniform_norm_coercivity
      K F htransport p k ht hε₀ hε₁ q
  linarith
end Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation
