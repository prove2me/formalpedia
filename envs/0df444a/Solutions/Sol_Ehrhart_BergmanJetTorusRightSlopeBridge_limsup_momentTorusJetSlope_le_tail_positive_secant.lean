-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeBridge.limsup_momentTorusJetSlope_le_tail_positive_secant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/c56f72f9-7886-476a-b8c9-017914b4a6cb

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPointwiseLogKernel_tendsto_log_momentNormalized_diagonalKernel_div
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentTorusJetSlope_nonneg
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentTorusJetSlope_le_canonicalScale
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentPositiveTorusJetSlope_le_cover_positive_secant
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentPositiveJointGeodesic_le_tailUpperEnvelope

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
    (p : LogSpace n) (q : LogTorus n)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (hmax : ∀ x : Space n,
      phase u (momentNormalizedPotential F) x ≤
        phase u (momentNormalizedPotential F) q.1)
    (r : ℕ) {t : ℝ} (ht : 0 < t) :
    Filter.limsup
        (fun k : ℕ =>
          momentTorusJetSlope K F htransport p k q) atTop ≤
      (momentJointTailUpperEnvelope K F htransport p r
          (sourcePositiveJointTimePoint
            (sourceTorusCoverPoint q) t ht) -
        momentNormalizedPotential F q.1) / t := by
  let z := sourceTorusCoverPoint q
  let B := momentJointTailUpperEnvelope K F htransport p r
    (sourcePositiveJointTimePoint z t ht)
  have hcob := Filter.isCoboundedUnder_le_of_le atTop
    (fun k => momentTorusJetSlope_nonneg
      K F htransport p k q)
  have hbounded :
      Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun k : ℕ =>
          momentTorusJetSlope K F htransport p k q) :=
    Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall fun k =>
        momentTorusJetSlope_le_canonicalScale
          K F htransport p k q)
  change
    Filter.limsup
        (fun k : ℕ =>
          momentTorusJetSlope K F htransport p k q) atTop ≤
      (B - momentNormalizedPotential F q.1) / t
  apply (Filter.limsup_le_iff hcob hbounded).mpr
  intro a ha
  have hthreshold :
      B - a * t < momentNormalizedPotential F q.1 := by
    have hcross := (div_lt_iff₀ ht).mp ha
    linarith
  have hzero :=
    (tendsto_order.mp
      (tendsto_log_momentNormalized_diagonalKernel_div
        K F htransport hu q.1 hmax)).1
      (B - a * t) hthreshold
  filter_upwards
    [eventually_ge_atTop
      (momentJointTailStart K F htransport p + r + 1),
      hzero] with k hk hlog
  have hkpos : 0 < k := by omega
  have htail :
      momentJointTailStart K F htransport p + r ≤ k - 1 := by
    omega
  have hkadd : k - 1 + 1 = k := by omega
  let N := Nat.floor
    (BodyScale.canonicalScale K * (k : ℝ))
  have htime :
      momentJetGeodesic K hkpos F htransport p N z t ≤ B := by
    have hfinite :=
      momentPositiveJointGeodesic_le_tailUpperEnvelope
        K F htransport p r (k - 1) htail
          (sourcePositiveJointTimePoint z t ht)
    rw [momentPositiveJointGeodesic_eq_momentJetGeodesic,
      jointLogTime_sourcePositiveJointTimePoint] at hfinite
    simpa [hkadd, N, B, sourcePositiveJointTimePoint]
      using hfinite
  have hzeroeq :
      momentJetGeodesic K hkpos F htransport p N z 0 =
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) q.1) / (k : ℝ) := by
    rw [momentJetGeodesic_zero_eq_log_diagonalKernel,
      realLogCoordinate_sourceTorusCoverPoint]
  have hfiniteSlope :=
    momentPositiveTorusJetSlope_le_cover_positive_secant
      K hkpos F htransport p N q ht
  have hslope :
      momentTorusJetSlope K F htransport p k q ≤
        (B - Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) q.1) /
              (k : ℝ)) / t := by
    simp only [momentTorusJetSlope, dif_pos hkpos]
    change momentPositiveTorusJetSlope
      K hkpos F htransport p N q ≤ _
    calc
      momentPositiveTorusJetSlope
          K hkpos F htransport p N q ≤
        (momentJetGeodesic K hkpos F htransport p N z t -
          momentJetGeodesic K hkpos F htransport p N z 0) / t :=
        hfiniteSlope
      _ ≤
        (B - Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) q.1) /
              (k : ℝ)) / t := by
        rw [hzeroeq]
        exact (div_le_div_iff_of_pos_right ht).mpr
          (sub_le_sub_right htime _)
  apply lt_of_le_of_lt hslope
  apply (div_lt_iff₀ ht).mpr
  linarith
end Ehrhart.BergmanJetTorusRightSlopeBridge
