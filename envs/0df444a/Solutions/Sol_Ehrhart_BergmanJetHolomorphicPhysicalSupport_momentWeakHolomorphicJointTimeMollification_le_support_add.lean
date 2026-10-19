-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalSupport.momentWeakHolomorphicJointTimeMollification_le_support_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/8f6652d6-9d63-4718-aad1-452c69d9e744

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalSupport_momentWeakHolomorphicJointMollification_le_support_add

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetHolomorphicPhysicalSupport
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters WeightedTorusHilbert BergmanDiagonalBasisIndependence
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative JetEnvelopeTrueRadialMollifier
open EnvelopeSmoothing EnvelopeGeneralTorusDescent RadialPartitionBounds MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentWeakBergman BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetSpatialSmoothing
open BergmanJetStrictRadialRegularizer BergmanJetJointHolomorphicStrictSchur
open BergmanJetHolomorphicPhysicalMeasure WeightedTorusDolbeault WeightedTorusBrascampLieb
open ArbitraryBodyOneSidedAngularResolventDefect
open scoped BigOperators ENNReal Topology ContDiff Convolution
namespace Ehrhart.BergmanJetHolomorphicPhysicalSupport
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (k : ℕ) (t : ℝ) :
    momentWeakHolomorphicJointTrueRadialMollification
      K F htransport p k (sourceJointTimeEmbedding z t) ≤
      SupportFunction.supportFunction K.carrier
        (realLogCoordinate z) +
      momentWeakHolomorphicJointTimeSupportError K F t := by
  have h := momentWeakHolomorphicJointMollification_le_support_add
    K F htransport p k (sourceJointTimeEmbedding z t)
  have hspace :
      realLogCoordinate (sourceJointTimeEmbedding z t).1 =
        realLogCoordinate z := rfl
  rw [hspace] at h
  simpa [momentWeakHolomorphicJointTimeSupportError,
    momentWeakHolomorphicJointMollifierSupportError,
    sourceJointCoverTime_timeEmbedding] using h
end Ehrhart.BergmanJetHolomorphicPhysicalSupport
