-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeBridge.momentCoverMoment_zero_eq_torusTruncatedJetOrderDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/0b18e915-e1eb-4555-b651-178c2bcb192b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    exponentialMoment
        (momentHolomorphicBasisWeight
          K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p)
          (sourceTorusCoverPoint q))
        (momentTruncatedJetOrder K hk F htransport p N)
        1 0 =
      momentTorusTruncatedJetOrderDensity
        K hk F htransport p N q := by
  unfold exponentialMoment momentTorusTruncatedJetOrderDensity
  simp only [pow_one, zero_mul, Real.exp_zero, mul_one]
  apply Finset.sum_congr rfl
  intro i _
  unfold momentHolomorphicBasisWeight
    momentTorusJetBasisWeight
  rw [momentTorusRepresentative_eq_holomorphicRepresentative_cover]
  ring
end Ehrhart.BergmanJetTorusRightSlopeBridge
