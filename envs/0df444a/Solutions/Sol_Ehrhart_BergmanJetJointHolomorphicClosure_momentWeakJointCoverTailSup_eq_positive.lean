-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicClosure.momentWeakJointCoverTailSup_eq_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/9b30c906-8bc0-4037-882a-1f4f7cd776c4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicClosure_momentWeakJointCoverFiniteGeodesic_eq_positive

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
    (p : LogSpace n) (r : ℕ)
    (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    momentWeakJointCoverTailSup K F htransport p r q =
      momentJointTailSup K F htransport p r
        (sourceJointExpPositiveLift q hq) := by
  have hfamily :
      (fun j : ℕ => momentWeakJointCoverFiniteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + r + j) q) =
      (fun j : ℕ => momentPositiveJointGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + r + j)
            (sourceJointExpPositiveLift q hq)) := by
    funext j
    exact momentWeakJointCoverFiniteGeodesic_eq_positive
      K F htransport p
        (momentJointTailStart K F htransport p + r + j) q hq
  unfold momentWeakJointCoverTailSup momentJointTailSup
  rw [hfamily]
end Ehrhart.BergmanJetJointHolomorphicClosure
