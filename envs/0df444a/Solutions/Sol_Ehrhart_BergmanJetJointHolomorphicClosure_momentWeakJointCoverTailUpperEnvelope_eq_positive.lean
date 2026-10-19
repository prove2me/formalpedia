-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicClosure.momentWeakJointCoverTailUpperEnvelope_eq_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/228db4f8-5706-4e12-b75f-e0009e48d7cd

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeGlobalPlurisubharmonicClosure_upperRegularization_comp_isOpenMap
import Theorems.Thm_Ehrhart_JetEnvelopeGlobalPlurisubharmonicClosure_continuous_sourcePositiveCoverExp
import Theorems.Thm_Ehrhart_JetEnvelopeGlobalPlurisubharmonicClosure_isOpen_sourcePositiveCover
import Theorems.Thm_Ehrhart_JetEnvelopeGlobalPlurisubharmonicClosure_isOpenMap_sourcePositiveCoverExp
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicClosure_momentWeakJointCoverTailSup_eq_positive

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
    momentWeakJointCoverTailUpperEnvelope
      K F htransport p r q =
      momentJointTailUpperEnvelope K F htransport p r
        (sourceJointExpPositiveLift q hq) := by
  let Q : PositiveSourceJointComplexCover n := ⟨q, hq⟩
  have hopenval : IsOpenMap
      (fun y : PositiveSourceJointComplexCover n => y.val) :=
    (isOpen_sourcePositiveCover n).isOpenEmbedding_subtypeVal.isOpenMap
  have hcontval : Continuous
      (fun y : PositiveSourceJointComplexCover n => y.val) :=
    continuous_subtype_val
  have hregval := upperRegularization_comp_isOpenMap
    (momentWeakJointCoverTailSup K F htransport p r)
    (fun y : PositiveSourceJointComplexCover n => y.val)
    hcontval hopenval Q
  have hregexp := upperRegularization_comp_isOpenMap
    (momentJointTailSup K F htransport p r)
    (sourcePositiveCoverExp (n := n))
    (continuous_sourcePositiveCoverExp n)
    (isOpenMap_sourcePositiveCoverExp n) Q
  have hfun :
      (fun y : PositiveSourceJointComplexCover n =>
        momentWeakJointCoverTailSup K F htransport p r y.val) =
      (fun y : PositiveSourceJointComplexCover n =>
        momentJointTailSup K F htransport p r
          (sourcePositiveCoverExp y)) := by
    funext y
    exact momentWeakJointCoverTailSup_eq_positive
      K F htransport p r y.val y.property
  unfold momentWeakJointCoverTailUpperEnvelope
    momentJointTailUpperEnvelope
  calc
    upperRegularization
        (momentWeakJointCoverTailSup K F htransport p r) q =
      upperRegularization
        (fun y : PositiveSourceJointComplexCover n =>
          momentWeakJointCoverTailSup
            K F htransport p r y.val) Q := hregval.symm
    _ = upperRegularization
        (fun y : PositiveSourceJointComplexCover n =>
          momentJointTailSup K F htransport p r
            (sourcePositiveCoverExp y)) Q := by rw [hfun]
    _ = upperRegularization
        (momentJointTailSup K F htransport p r)
          (sourcePositiveCoverExp Q) := hregexp
    _ = upperRegularization
        (momentJointTailSup K F htransport p r)
          (sourceJointExpPositiveLift q hq) := by rfl
end Ehrhart.BergmanJetJointHolomorphicClosure
