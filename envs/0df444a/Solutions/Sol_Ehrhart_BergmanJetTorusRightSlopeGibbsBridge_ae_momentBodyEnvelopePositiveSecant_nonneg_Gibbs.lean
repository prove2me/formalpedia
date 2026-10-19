-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeGibbsBridge.ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/cc83dc78-4806-4d04-b68e-e384e702d60a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentTorusJetSlope_nonneg
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentTorusJetSlope_le_canonicalScale
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeGibbsBridge_ae_limsup_momentTorusJetSlope_le_bodySecant_Gibbs

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetTorusRightSlopeGibbsBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentRegularity
open BergmanJetTorusEnvelope BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge
open BergmanJetTorusRightSlopeBridge
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetTorusRightSlopeGibbsBridge
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ q : LogTorus n
      ∂(sourceProbability (momentBodyTorusWeight K p) 0),
      0 ≤ momentBodyEnvelopePositiveSecant K p t q := by
  filter_upwards
    [ae_limsup_momentTorusJetSlope_le_bodySecant_Gibbs
      K p ht] with q hq
  have hbounded :
      Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun k : ℕ => momentTorusJetSlope
          K (momentBodyOptimizer K)
            (momentBodyOptimizer_transport K) p k q) :=
    Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall fun k =>
        momentTorusJetSlope_le_canonicalScale
          K (momentBodyOptimizer K)
            (momentBodyOptimizer_transport K) p k q)
  have hnonneg :
      0 ≤ Filter.limsup
        (fun k : ℕ => momentTorusJetSlope
          K (momentBodyOptimizer K)
            (momentBodyOptimizer_transport K) p k q) atTop :=
    Filter.le_limsup_of_frequently_le
      (Filter.Eventually.of_forall fun k =>
        momentTorusJetSlope_nonneg
          K (momentBodyOptimizer K)
            (momentBodyOptimizer_transport K) p k q).frequently
      hbounded
  exact hnonneg.trans hq
end Ehrhart.BergmanJetTorusRightSlopeGibbsBridge
