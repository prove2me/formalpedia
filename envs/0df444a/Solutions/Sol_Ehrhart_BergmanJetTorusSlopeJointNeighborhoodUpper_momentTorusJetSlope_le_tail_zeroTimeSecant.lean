-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper.momentTorusJetSlope_le_tail_zeroTimeSecant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/dcdd2f88-6596-455f-b2b7-232c4d7f872e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentPositiveTorusJetSlope_le_cover_positive_secant
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentPositiveJointGeodesic_le_tailUpperEnvelope

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert BergmanMonomials JetEnvelopeRightDerivative
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakBergman
open BergmanJetRealGeodesic BergmanJetUpperEnvelope BergmanJetTorusSlopeBridge
open BergmanJetTorusRightSlopeBridge BergmanJetGlobalLogKernelEquiLipschitz
open BergmanJetPortmanteauActualUpperTailBridge
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r k : ℕ)
    (hk : momentJointTailStart K F htransport p + r + 1 ≤ k)
    (q : LogTorus n) (t : ℝ) (ht : 0 < t) :
    momentTorusJetSlope K F htransport p k q ≤
      (momentTorusTailUpperEnvelopeTimeSlice
          K F htransport p r t ht q -
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) q.1) /
              (k : ℝ)) / t := by
  have hkpos : 0 < k := by omega
  have htail :
      momentJointTailStart K F htransport p + r ≤ k - 1 := by
    omega
  have hkadd : k - 1 + 1 = k := by omega
  let z := sourceTorusCoverPoint q
  let N := Nat.floor
    (BodyScale.canonicalScale K * (k : ℝ))
  let B := momentTorusTailUpperEnvelopeTimeSlice
    K F htransport p r t ht q
  have htime :
      momentJetGeodesic K hkpos F htransport p N z t ≤ B := by
    have hfinite :=
      momentPositiveJointGeodesic_le_tailUpperEnvelope
        K F htransport p r (k - 1) htail
          (sourcePositiveJointTimePoint z t ht)
    rw [momentPositiveJointGeodesic_eq_momentJetGeodesic,
      jointLogTime_sourcePositiveJointTimePoint] at hfinite
    simpa [hkadd, N, B, z,
      momentTorusTailUpperEnvelopeTimeSlice,
      sourcePositiveJointTimePoint] using hfinite
  have hzeroeq :
      momentJetGeodesic K hkpos F htransport p N z 0 =
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) q.1) / (k : ℝ) := by
    rw [momentJetGeodesic_zero_eq_log_diagonalKernel]
    exact congrArg
      (fun x : Space n =>
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) x) / (k : ℝ))
      (realLogCoordinate_sourceTorusCoverPoint q)
  have hfiniteSlope :=
    momentPositiveTorusJetSlope_le_cover_positive_secant
      K hkpos F htransport p N q ht
  change momentTorusJetSlope K F htransport p k q ≤
    (B - Real.log
      (diagonalKernel K k
        (momentNormalizedPotential F) q.1) / (k : ℝ)) / t
  simp only [momentTorusJetSlope, dif_pos hkpos]
  change momentPositiveTorusJetSlope
    K hkpos F htransport p N q ≤ _
  calc
    momentPositiveTorusJetSlope
        K hkpos F htransport p N q ≤
      (momentJetGeodesic K hkpos F htransport p N z t -
        momentJetGeodesic K hkpos F htransport p N z 0) / t :=
      hfiniteSlope
    _ ≤ (B - Real.log
        (diagonalKernel K k
          (momentNormalizedPotential F) q.1) / (k : ℝ)) / t := by
      rw [hzeroeq]
      exact (div_le_div_iff_of_pos_right ht).mpr
        (sub_le_sub_right htime _)
end Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper
