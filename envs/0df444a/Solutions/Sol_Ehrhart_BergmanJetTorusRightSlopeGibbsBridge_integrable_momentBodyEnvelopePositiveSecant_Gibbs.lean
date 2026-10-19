-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeGibbsBridge.integrable_momentBodyEnvelopePositiveSecant_Gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/7c1cc1ae-f299-4aa6-8b91-17f593075c04

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeGibbsBridge_momentBodyEnvelopePositiveSecant_le_canonicalScale
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeGibbsBridge_measurable_momentBodyEnvelopePositiveSecant
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeGibbsBridge_ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs

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
    Integrable (momentBodyEnvelopePositiveSecant K p t)
      (sourceProbability (momentBodyTorusWeight K p) 0) := by
  let := sourceProbability_momentBody_isProbability K p 0
  refine (integrable_const (BodyScale.canonicalScale K)).mono'
    (measurable_momentBodyEnvelopePositiveSecant
      K p t).aestronglyMeasurable ?_
  filter_upwards
    [ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs
      K p ht] with q hq
  rw [Real.norm_eq_abs, abs_of_nonneg hq]
  exact momentBodyEnvelopePositiveSecant_le_canonicalScale
    K p ht q
end Ehrhart.BergmanJetTorusRightSlopeGibbsBridge
