-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeBridge.momentPositiveTorusJetSlope_le_canonicalScale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/eab544d1-ca49-4194-8340-b79e202534f6

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentPositiveTorusJetSlope_le_cutoff

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
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : LogTorus n) :
    momentPositiveTorusJetSlope
        K hk F htransport p
          (Nat.floor
            (BodyScale.canonicalScale K * (k : ℝ))) q ≤
      BodyScale.canonicalScale K := by
  have hkreal : 0 < (k : ℝ) := by
    exact_mod_cast hk
  calc
    momentPositiveTorusJetSlope
        K hk F htransport p
          (Nat.floor
            (BodyScale.canonicalScale K * (k : ℝ))) q ≤
      ((Nat.floor
          (BodyScale.canonicalScale K * (k : ℝ)) : ℕ) : ℝ) /
        (k : ℝ) :=
      momentPositiveTorusJetSlope_le_cutoff
        K hk F htransport p _ q
    _ ≤ BodyScale.canonicalScale K :=
      (div_le_iff₀ hkreal).mpr
        (Nat.floor_le
          (mul_nonneg
            (BodyScale.canonicalScale_pos K).le hkreal.le))
end Ehrhart.BergmanJetTorusRightSlopeBridge
