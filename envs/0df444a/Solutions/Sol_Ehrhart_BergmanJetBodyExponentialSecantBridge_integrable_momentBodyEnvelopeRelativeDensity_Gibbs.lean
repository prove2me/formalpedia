-- Prove2me | solution 1 for Ehrhart.BergmanJetBodyExponentialSecantBridge.integrable_momentBodyEnvelopeRelativeDensity_Gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/e7c0d774-fdda-47be-a429-fffcee280d82

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetBodyExponentialSecantBridge_measurable_momentBodyEnvelopeRelativeDensity
import Theorems.Thm_Ehrhart_BergmanJetBodyExponentialSecantBridge_momentBodyEnvelopeRelativeDensity_pos
import Theorems.Thm_Ehrhart_BergmanJetBodyExponentialSecantBridge_ae_momentBodyEnvelopeRelativeDensity_le_one

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetBodyExponentialSecantBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity
open BergmanJetPartitionEndpoint BergmanJetTorusRightSlopeGibbsBridge
open BergmanJetBodyLogPartitionSharpGrowth
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetBodyExponentialSecantBridge
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    Integrable (momentBodyEnvelopeRelativeDensity K p t)
      (sourceProbability (momentBodyTorusWeight K p) 0) := by
  let := sourceProbability_momentBody_isProbability K p 0
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_momentBodyEnvelopeRelativeDensity
      K p t).aestronglyMeasurable ?_
  filter_upwards
    [ae_momentBodyEnvelopeRelativeDensity_le_one
      K p ht] with q hq
  rw [Real.norm_eq_abs, abs_of_pos
    (momentBodyEnvelopeRelativeDensity_pos K p t q)]
  exact hq
end Ehrhart.BergmanJetBodyExponentialSecantBridge
