-- Prove2me | solution 1 for Ehrhart.BergmanJetBodyExponentialSecantBridge.integral_momentBodyEnvelopePositiveSecant_le_partition_complement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/3f68cea6-d160-4c98-abf0-521b3f87f6ab

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeGibbsBridge_momentBodyEnvelopePositiveSecant_le_canonicalScale
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeGibbsBridge_ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeGibbsBridge_integrable_momentBodyEnvelopePositiveSecant_Gibbs
import Theorems.Thm_Ehrhart_BergmanJetBodyExponentialSecantBridge_nonnegative_le_exp_mul_one_sub_exp_neg
import Theorems.Thm_Ehrhart_BergmanJetBodyExponentialSecantBridge_integral_momentBodyEnvelopeRelativeDensity_eq_normalizedPartition
import Theorems.Thm_Ehrhart_BergmanJetBodyExponentialSecantBridge_integrable_momentBodyEnvelopeRelativeDensity_Gibbs

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
    (∫ q : LogTorus n,
      momentBodyEnvelopePositiveSecant K p t q
        ∂(sourceProbability (momentBodyTorusWeight K p) 0)) ≤
      Real.exp (BodyScale.canonicalScale K * t) *
        (1 - momentBodyNormalizedPartition K p t) / t := by
  let μ := sourceProbability (momentBodyTorusWeight K p) 0
  let C := BodyScale.canonicalScale K
  let := sourceProbability_momentBody_isProbability K p 0
  have hrelint :=
    integrable_momentBodyEnvelopeRelativeDensity_Gibbs K p ht
  have hrightint :
      Integrable
        (fun q : LogTorus n =>
          Real.exp (C * t) *
            (1 - momentBodyEnvelopeRelativeDensity K p t q) / t)
        μ := by
    exact
      (((integrable_const (1 : ℝ)).sub hrelint).const_mul
        (Real.exp (C * t))).div_const t
  have hpoint :
      ∀ᵐ q : LogTorus n ∂μ,
        momentBodyEnvelopePositiveSecant K p t q ≤
          Real.exp (C * t) *
            (1 - momentBodyEnvelopeRelativeDensity K p t q) / t := by
    filter_upwards
      [ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs
        K p ht] with q hq
    let u := momentBodyTorusWeight K p t q -
      momentBodyTorusWeight K p 0 q
    have hid :
        momentBodyEnvelopePositiveSecant K p t q * t = u := by
      simp [momentBodyEnvelopePositiveSecant, u, ht.ne']
    have hu : 0 ≤ u := by
      rw [← hid]
      exact mul_nonneg hq ht.le
    have huC : u ≤ C * t := by
      rw [← hid]
      exact mul_le_mul_of_nonneg_right
        (momentBodyEnvelopePositiveSecant_le_canonicalScale
          K p ht q) ht.le
    have hsandwich :=
      nonnegative_le_exp_mul_one_sub_exp_neg hu huC
    change
      (momentBodyTorusWeight K p t q -
        momentBodyTorusWeight K p 0 q) / t ≤
        Real.exp (C * t) *
          (1 - Real.exp
            (-(momentBodyTorusWeight K p t q -
              momentBodyTorusWeight K p 0 q))) / t
    exact (div_le_div_iff_of_pos_right ht).mpr hsandwich
  have hint := integral_mono_ae
    (integrable_momentBodyEnvelopePositiveSecant_Gibbs
      K p ht) hrightint hpoint
  have heq :
      (∫ q : LogTorus n,
        Real.exp (C * t) *
          (1 - momentBodyEnvelopeRelativeDensity K p t q) / t
        ∂μ) =
        Real.exp (C * t) *
          (1 - momentBodyNormalizedPartition K p t) / t := by
    rw [MeasureTheory.integral_div,
      MeasureTheory.integral_const_mul,
      MeasureTheory.integral_sub
        (integrable_const (1 : ℝ)) hrelint,
      integral_momentBodyEnvelopeRelativeDensity_eq_normalizedPartition]
    simp
  change
    (∫ q : LogTorus n,
      momentBodyEnvelopePositiveSecant K p t q ∂μ) ≤ _
  rw [← heq]
  exact hint
end Ehrhart.BergmanJetBodyExponentialSecantBridge
