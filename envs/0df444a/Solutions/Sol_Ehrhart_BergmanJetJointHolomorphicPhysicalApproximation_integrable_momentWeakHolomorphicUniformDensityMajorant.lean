-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation.integrable_momentWeakHolomorphicUniformDensityMajorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/3095bdfd-48c6-439e-937c-103f622d28b3

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhysicalApproximation_momentWeakHolomorphicUniformRadialRate_pos

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
      normalizedTargetBodyMeasure K) :
    Integrable
      (momentWeakHolomorphicUniformDensityMajorant
        K F htransport)
      (sourceTorusBaseMeasure n) := by
  have hrad : Integrable
      (fun x : Space n =>
        Real.exp
          (-momentWeakHolomorphicUniformRadialRate K * ‖x‖))
      (volume : Measure (Space n)) :=
    integrable_exp_neg_mul_norm_all
      (momentWeakHolomorphicUniformRadialRate_pos K)
  have hang : Integrable
      (fun _ : AngularTorus n => (1 : ℝ))
      (angularMeasure n) :=
    integrable_const 1
  have hprod : Integrable
      (fun q : LogTorus n =>
        Real.exp
          (-momentWeakHolomorphicUniformRadialRate K * ‖q.1‖) *
            (1 : ℝ))
      (sourceTorusBaseMeasure n) := by
    simpa [sourceTorusBaseMeasure] using hrad.mul_prod hang
  change Integrable
    (fun q : LogTorus n =>
      Real.exp
          (momentWeakHolomorphicUniformCoercivityConstant
            K F htransport) *
        (Real.exp
          (-momentWeakHolomorphicUniformRadialRate K * ‖q.1‖) *
            (1 : ℝ)))
    (sourceTorusBaseMeasure n)
  exact hprod.const_mul
    (Real.exp
      (momentWeakHolomorphicUniformCoercivityConstant
        K F htransport))
end Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation
