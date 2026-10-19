-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeBridge.continuous_momentTorusJetSlope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/c9fd4c34-039c-42e6-b3fb-2cbb783a2fc8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_continuous_momentPositiveTorusJetSlope

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
    (p : LogSpace n) (k : ℕ) :
    Continuous (momentTorusJetSlope K F htransport p k) := by
  classical
  change
    Continuous (fun q : LogTorus n =>
      if hk : 0 < k then
        momentPositiveTorusJetSlope
          K hk F htransport p
            (Nat.floor
              (BodyScale.canonicalScale K * (k : ℝ))) q
      else 0)
  by_cases hk : 0 < k
  · simpa [hk] using
      (continuous_momentPositiveTorusJetSlope
        K hk F htransport p
        (Nat.floor
          (BodyScale.canonicalScale K * (k : ℝ))))
  · simpa [hk] using
      (continuous_const :
        Continuous (fun _ : LogTorus n => (0 : ℝ)))
end Ehrhart.BergmanJetTorusRightSlopeBridge
