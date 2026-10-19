-- Prove2me | solution 1 for Ehrhart.BergmanJetBodyExponentialSecantBridge.ae_momentBodyEnvelopeRelativeDensity_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/a128aa01-e164-4690-b675-99772167562b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeGibbsBridge_ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs

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
    ∀ᵐ q : LogTorus n
      ∂(sourceProbability (momentBodyTorusWeight K p) 0),
      momentBodyEnvelopeRelativeDensity K p t q ≤ 1 := by
  filter_upwards
    [ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs
      K p ht] with q hq
  unfold momentBodyEnvelopeRelativeDensity
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have hmul := mul_nonneg hq ht.le
  have hid :
      momentBodyEnvelopePositiveSecant K p t q * t =
        momentBodyTorusWeight K p t q -
          momentBodyTorusWeight K p 0 q := by
    simp [momentBodyEnvelopePositiveSecant, ht.ne']
  linarith
end Ehrhart.BergmanJetBodyExponentialSecantBridge
