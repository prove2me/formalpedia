-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicClosure.momentWeakJointCoverUpperEnvelope_eq_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/e544a8e4-bb0f-473f-ad96-4818e19268f0

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicClosure_momentWeakJointCoverTailUpperEnvelope_eq_positive

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
    momentWeakJointCoverUpperEnvelope K F htransport p q =
      momentJointUpperEnvelope K F htransport p
        (sourceJointExpPositiveLift q hq) := by
  unfold momentWeakJointCoverUpperEnvelope momentJointUpperEnvelope
  simp_rw [momentWeakJointCoverTailUpperEnvelope_eq_positive
    K F htransport p _ q hq]
end Ehrhart.BergmanJetJointHolomorphicClosure
