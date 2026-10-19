-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.sourceFree_integral_sourceProbability_eq_density_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/f6b55ac8-62aa-492c-a0d3-c6d0f61dd2af

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
    (hpart : 0 < sourcePartition a t)
    (F : LogTorus n → ℝ) :
    (∫ q : LogTorus n, F q ∂(sourceProbability a t)) =
      ∫ q : LogTorus n,
        F q * sourceNormalizedDensity a t q
          ∂(sourceTorusBaseMeasure n) := by
  have hcontinuous : Continuous (sourceNormalizedDensity a t) :=
    (Real.continuous_exp.comp ha.neg).div_const _
  have hmeas : Measurable
      (fun q : LogTorus n =>
        ENNReal.ofReal (sourceNormalizedDensity a t q)) :=
    ENNReal.measurable_ofReal.comp hcontinuous.measurable
  have hfinite :
      ∀ᵐ q ∂(sourceTorusBaseMeasure n),
        ENNReal.ofReal (sourceNormalizedDensity a t q) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [sourceProbability,
    integral_withDensity_eq_integral_toReal_smul hmeas hfinite]
  apply integral_congr_ae
  filter_upwards [] with q
  have hpos : 0 ≤ sourceNormalizedDensity a t q :=
    (div_pos (Real.exp_pos _) hpart).le
  rw [ENNReal.toReal_ofReal hpos]
  simp [smul_eq_mul, mul_comm]
end Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
