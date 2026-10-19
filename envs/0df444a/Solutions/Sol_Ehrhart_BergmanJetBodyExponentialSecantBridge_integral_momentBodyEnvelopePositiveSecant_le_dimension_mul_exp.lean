-- Prove2me | solution 1 for Ehrhart.BergmanJetBodyExponentialSecantBridge.integral_momentBodyEnvelopePositiveSecant_le_dimension_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/14b7aba1-3cb6-497c-9948-27ad7de97aec

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetBodyExponentialSecantBridge_one_sub_momentBodyNormalizedPartition_le_dimension_mul
import Theorems.Thm_Ehrhart_BergmanJetBodyExponentialSecantBridge_integral_momentBodyEnvelopePositiveSecant_le_partition_complement

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
    {t : ℝ} (ht : 0 < t) :
    (∫ q : LogTorus n,
      momentBodyEnvelopePositiveSecant
        K (0 : LogSpace n) t q
        ∂(sourceProbability
          (momentBodyTorusWeight K (0 : LogSpace n)) 0)) ≤
      (n : ℝ) *
        Real.exp (BodyScale.canonicalScale K * t) := by
  have hfirst :=
    integral_momentBodyEnvelopePositiveSecant_le_partition_complement
      K (0 : LogSpace n) ht
  have hcomp :=
    one_sub_momentBodyNormalizedPartition_le_dimension_mul
      K ht.le
  have hratio :
      (1 - momentBodyNormalizedPartition
        K (0 : LogSpace n) t) / t ≤ (n : ℝ) :=
    (div_le_iff₀ ht).mpr hcomp
  calc
    (∫ q : LogTorus n,
      momentBodyEnvelopePositiveSecant
        K (0 : LogSpace n) t q
        ∂(sourceProbability
          (momentBodyTorusWeight K (0 : LogSpace n)) 0)) ≤
      Real.exp (BodyScale.canonicalScale K * t) *
        (1 - momentBodyNormalizedPartition
          K (0 : LogSpace n) t) / t := hfirst
    _ = Real.exp (BodyScale.canonicalScale K * t) *
          ((1 - momentBodyNormalizedPartition
            K (0 : LogSpace n) t) / t) := by ring
    _ ≤ Real.exp (BodyScale.canonicalScale K * t) *
          (n : ℝ) :=
      mul_le_mul_of_nonneg_left hratio
        (Real.exp_pos _).le
    _ = (n : ℝ) *
          Real.exp (BodyScale.canonicalScale K * t) := by ring
end Ehrhart.BergmanJetBodyExponentialSecantBridge
