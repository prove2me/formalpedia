-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeGibbsBridge.momentBodyEnvelopePositiveSecant_le_canonicalScale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/270ec849-c6f2-4124-9737-2cc802afbc4b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusEnvelope_momentTorusEnvelopeTimeSlice_le_normalized_add

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
    (p : LogSpace n) {t : ℝ} (ht : 0 < t)
    (q : LogTorus n) :
    momentBodyEnvelopePositiveSecant K p t q ≤
      BodyScale.canonicalScale K := by
  unfold momentBodyEnvelopePositiveSecant
  apply (div_le_iff₀ ht).mpr
  rw [momentBodyTorusWeight_zero]
  have h := momentTorusEnvelopeTimeSlice_le_normalized_add
    K (momentBodyOptimizer K)
      (momentBodyOptimizer_transport K) p q ht
  change
    momentBodyTorusWeight K p t q ≤
      momentNormalizedPotential (momentBodyOptimizer K) q.1 +
        BodyScale.canonicalScale K * t at h
  linarith
end Ehrhart.BergmanJetTorusRightSlopeGibbsBridge
