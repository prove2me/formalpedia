-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicApproximation.tendsto_momentWeakHolomorphicJointTrueRadialMollification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/aabf29a0-fd60-4368-a522-960c6aa12a6d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeTrueRadialMollifier_tendsto_sourceJointTrueRadialSmoothed_of_upperSemicontinuousAt_and_le
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicApproximation_momentWeakJointCoverUpperEnvelope_le_trueRadialMollification

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetJointHolomorphicApproximation
open Set Function Filter MeasureTheory Metric
open TorusCharacters MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetJointHolomorphicClosure BergmanJetJointHolomorphicPlurisubharmonicSmoothing
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeTrueRadialMollifier
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder
attribute [local instance] Ehrhart.BergmanJetJointHolomorphicApproximation.sourceJointCoverVolume_isAddHaar
namespace Ehrhart.BergmanJetJointHolomorphicApproximation
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : SourceJointComplexCover n) :
    Tendsto
      (fun k : ℕ =>
        momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k q)
      atTop
        (𝓝 (momentWeakJointCoverUpperEnvelope
          K F htransport p q)) := by
  apply tendsto_sourceJointTrueRadialSmoothed_of_upperSemicontinuousAt_and_le
    (locallyIntegrable_momentWeakJointCoverUpperEnvelope
      K F htransport p) q
    (upperSemicontinuous_momentWeakJointCoverUpperEnvelope
      K F htransport p q)
  intro k
  exact momentWeakJointCoverUpperEnvelope_le_trueRadialMollification
    K F htransport p k q
end Ehrhart.BergmanJetJointHolomorphicApproximation
