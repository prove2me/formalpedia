-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicClosure.momentWeakJointCoverEnvelope_eq_upperEnvelope_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/74a89163-0772-4d13-88c3-e9a7877ac7aa

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhase_momentWeakJointCoverEnvelope_eq_holomorphicExpLift_of_pos
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicClosure_momentWeakJointCoverUpperEnvelope_eq_positive

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetJointHolomorphicClosure
open Set Function Filter MeasureTheory Metric
open TorusCharacters BergmanMonomials BergmanDiagonalBasisIndependence MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakBergman BergmanJetGeodesic
open BergmanJetRealGeodesic BergmanJetUpperEnvelope BergmanJetEnvelopePlurisubharmonic
open BergmanJetEnvelopeLimit BergmanJetJointEnvelopeRegularization BergmanJetJointHolomorphicPhase
open ActualJetUpperEnvelope ActualJetPlurisubharmonicEnvelope JetEnvelopeRightDerivative
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeGlobalPlurisubharmonicClosure
open BergmanGeodesicConvexity
open scoped BigOperators ENNReal Topology InnerProductSpace
namespace Ehrhart.BergmanJetJointHolomorphicClosure
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n)
    (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    momentWeakJointCoverEnvelope K F htransport p q =
      momentWeakJointCoverUpperEnvelope
        K F htransport p q := by
  rw [momentWeakJointCoverEnvelope_eq_holomorphicExpLift_of_pos
    K F htransport p q hq,
    momentWeakJointCoverUpperEnvelope_eq_positive
      K F htransport p q hq]
end Ehrhart.BergmanJetJointHolomorphicClosure
