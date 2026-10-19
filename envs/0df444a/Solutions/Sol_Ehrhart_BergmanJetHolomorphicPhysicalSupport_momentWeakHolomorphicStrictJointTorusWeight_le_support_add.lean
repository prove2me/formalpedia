-- Prove2me | solution 1 for Ehrhart.BergmanJetHolomorphicPhysicalSupport.momentWeakHolomorphicStrictJointTorusWeight_le_support_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/02563228-74f9-47f1-ae87-5dc5e836adec

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetStrictRadialRegularizer_momentBodyStrictRadialPotential_le_support_add
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalSupport_momentWeakHolomorphicJointTimeMollification_le_support_add

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
    (p : LogSpace n) (k : ℕ) (t : ℝ)
    {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (q : LogTorus n) :
    momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k t q ≤
      SupportFunction.supportFunction K.carrier q.1 +
      ((1 - ε) *
          momentWeakHolomorphicJointTimeSupportError K F t +
        ε * ((n : ℝ) * Real.log 2)) := by
  have hweak :=
    momentWeakHolomorphicJointTimeMollification_le_support_add
      K F htransport p (sourceTorusCoverPoint q) k t
  rw [realLogCoordinate_sourceTorusCoverPoint] at hweak
  have hstrict :=
    momentBodyStrictRadialPotential_le_support_add K q.1
  have hweak' := mul_le_mul_of_nonneg_left hweak
    (sub_nonneg.mpr hε₁)
  have hstrict' := mul_le_mul_of_nonneg_left hstrict hε₀
  rw [momentWeakHolomorphicStrictJointTorusWeight,
    jointSourceTorusWeight_eq_cover]
  unfold momentWeakHolomorphicStrictJointCoverWeight
  have href :
      MatrixTorusBochnerBridge.matrixSourceCoverPotential
        (momentBodyStrictRadialPotential K)
        (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t).1 =
        momentBodyStrictRadialPotential K q.1 := by
    simp [sourceJointTimeEmbedding, sourceTorusCoverPoint,
      MatrixTorusBochnerBridge.matrixSourceCoverPotential_logarithmicPoint]
  rw [href]
  nlinarith
end Ehrhart.BergmanJetHolomorphicPhysicalSupport
