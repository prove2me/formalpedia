-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeBridge.continuous_momentPositiveTorusJetSlope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/db7dadb6-548b-4b97-8e45-4e06463c3d41

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusSlopeBridge_continuous_momentTorusTruncatedJetOrderDensity
import Theorems.Thm_Ehrhart_BergmanJetTorusSlopeBridge_continuous_momentDiagonalKernel

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
    (p : LogSpace n) (N : ℕ) :
    Continuous
      (momentPositiveTorusJetSlope
        K hk F htransport p N) := by
  have hkreal : 0 < (k : ℝ) := by
    exact_mod_cast hk
  unfold momentPositiveTorusJetSlope
  apply
    (continuous_momentTorusTruncatedJetOrderDensity
      K hk F htransport p N).div
      (continuous_const.mul
        ((continuous_momentDiagonalKernel K hk F).comp
          continuous_fst))
  intro q
  exact
    (mul_pos hkreal
      (diagonalKernel_momentNormalized_pos
        K hk F htransport q.1)).ne'
end Ehrhart.BergmanJetTorusRightSlopeBridge
