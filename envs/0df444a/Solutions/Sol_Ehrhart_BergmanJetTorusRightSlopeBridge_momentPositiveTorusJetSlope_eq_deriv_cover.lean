-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeBridge.momentPositiveTorusJetSlope_eq_deriv_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/1c6d6286-aa03-4760-9020-85615db6dd31

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentCoverMoment_zero_eq_torusTruncatedJetOrderDensity
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentCoverPartition_zero_eq_diagonalKernel

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
      K hk F htransport p N q =
        deriv
          (momentJetGeodesic K hk F htransport p N
            (sourceTorusCoverPoint q)) 0 := by
  unfold momentJetGeodesic
  rw [(hasDerivAt_logarithmicPotential
    (momentHolomorphicBasisWeight
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p)
      (sourceTorusCoverPoint q))
    (momentTruncatedJetOrder K hk F htransport p N)
    (momentHolomorphicBasisWeight_nonneg
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p)
      (sourceTorusCoverPoint q))
    (exists_positive_momentHolomorphicBasisWeight
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p)
      (sourceTorusCoverPoint q))
    (k : ℝ) 0).deriv]
  rw [momentCoverMoment_zero_eq_torusTruncatedJetOrderDensity
    K hk F htransport p N q,
    momentCoverPartition_zero_eq_diagonalKernel
      K hk F htransport p N q]
  unfold momentPositiveTorusJetSlope
  ring
end Ehrhart.BergmanJetTorusRightSlopeBridge
