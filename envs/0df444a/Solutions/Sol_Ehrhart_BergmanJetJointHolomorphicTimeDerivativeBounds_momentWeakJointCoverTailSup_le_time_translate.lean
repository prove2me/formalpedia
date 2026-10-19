-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.momentWeakJointCoverTailSup_le_time_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/3ce257cc-d6fc-4454-abf1-ce8475303e05

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicTimeDerivativeBounds_momentWeakJointCoverFiniteGeodesic_le_time_translate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert MatrixTorusBochnerBridge MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation BergmanJetEnvelopePlurisubharmonic
open BergmanJetUpperEnvelope BergmanJetStrictRadialRegularizer BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetJointHolomorphicStrictSchur
open ActualJetUpperEnvelope JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative
open JetEnvelopeTrueRadialMollifier EnvelopeSmoothing EnvelopeGeneralTorusDescent
open RadialAccelerationBounds
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder
attribute [local instance] Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.sourceJointCoverVolume_isAddHaar
namespace Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (q : SourceJointComplexCover n) :
    momentWeakJointCoverTailSup K F htransport p r q ≤
      momentWeakJointCoverTailSup K F htransport p r
        (q + momentWeakJointRealTimeShift n h) := by
  unfold momentWeakJointCoverTailSup
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  calc
    momentWeakJointCoverFiniteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + r + j) q ≤
      momentWeakJointCoverFiniteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + r + j)
          (q + momentWeakJointRealTimeShift n h) :=
      momentWeakJointCoverFiniteGeodesic_le_time_translate
        K F htransport p _ hh q
    _ ≤ sSup (Set.range fun i : ℕ =>
        momentWeakJointCoverFiniteGeodesic
          K F htransport p
            (momentJointTailStart K F htransport p + r + i)
            (q + momentWeakJointRealTimeShift n h)) := by
      apply le_csSup
        (momentWeakJointCoverTailSup_range_bddAbove
          K F htransport p r
            (q + momentWeakJointRealTimeShift n h))
      exact ⟨j, rfl⟩
end Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
