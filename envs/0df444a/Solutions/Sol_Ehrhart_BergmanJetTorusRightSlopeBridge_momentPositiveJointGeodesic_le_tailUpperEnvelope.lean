-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeBridge.momentPositiveJointGeodesic_le_tailUpperEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/62099408-269a-41e3-a988-e7484c9d5863

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetTorusRightSlopeBridge
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert SupportFunction LaplaceAsymptotics BergmanMonomials
open BergmanGeodesicConvexity JetEnvelopeRightDerivative ActualJetUpperEnvelope MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakGlobalKernel
open BergmanJetGeodesic BergmanJetProfileBridge BergmanJetRealGeodesic BergmanJetUpperEnvelope
open BergmanJetEnvelopeLimit BergmanJetTorusEnvelope BergmanJetTorusSlopeBridge
open BergmanJetPointwiseLogKernel
open scoped BigOperators ENNReal InnerProductSpace Topology
namespace Ehrhart.BergmanJetTorusRightSlopeBridge
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r k : ℕ)
    (hk : momentJointTailStart K F htransport p + r ≤ k)
    (w : PositiveJointLogSpace n) :
    momentPositiveJointGeodesic K F htransport p k w ≤
      momentJointTailUpperEnvelope K F htransport p r w := by
  calc
    momentPositiveJointGeodesic K F htransport p k w ≤
      momentJointTailSup K F htransport p r w := by
      unfold momentJointTailSup
      apply le_csSup
        (momentJointTailSup_range_bddAbove
          K F htransport p r w)
      refine ⟨k - (momentJointTailStart
        K F htransport p + r), ?_⟩
      change
        momentPositiveJointGeodesic K F htransport p
          (momentJointTailStart K F htransport p + r +
            (k - (momentJointTailStart
              K F htransport p + r))) w =
          momentPositiveJointGeodesic K F htransport p k w
      rw [Nat.add_sub_of_le hk]
    _ ≤ momentJointTailUpperEnvelope K F htransport p r w :=
      ActualJetUpperEnvelope.le_upperRegularization
        (momentJointTailSup K F htransport p r) w
        (momentJointTailSup_localUpperBounds_nonempty
          K F htransport p r w)
end Ehrhart.BergmanJetTorusRightSlopeBridge
