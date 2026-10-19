-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeBridge.momentPositiveTorusJetSlope_le_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/41ad89b5-1e33-4450-8a09-46447f1f2012

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentTorusTruncatedJetOrderDensity_le_diagonal_mul_cutoff

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
    (p : LogSpace n) (N : ℕ) (q : LogTorus n) :
    momentPositiveTorusJetSlope
        K hk F htransport p N q ≤
      (N : ℝ) / (k : ℝ) := by
  have hkreal : 0 < (k : ℝ) := by
    exact_mod_cast hk
  have hdiag :=
    diagonalKernel_momentNormalized_pos
      K hk F htransport q.1
  unfold momentPositiveTorusJetSlope
  apply (div_le_iff₀ (mul_pos hkreal hdiag)).mpr
  calc
    momentTorusTruncatedJetOrderDensity
        K hk F htransport p N q ≤
      (N : ℝ) * diagonalKernel K k
        (momentNormalizedPotential F) q.1 :=
      momentTorusTruncatedJetOrderDensity_le_diagonal_mul_cutoff
        K hk F htransport p N q
    _ = ((N : ℝ) / (k : ℝ)) *
        ((k : ℝ) * diagonalKernel K k
          (momentNormalizedPotential F) q.1) := by
      field_simp
end Ehrhart.BergmanJetTorusRightSlopeBridge
