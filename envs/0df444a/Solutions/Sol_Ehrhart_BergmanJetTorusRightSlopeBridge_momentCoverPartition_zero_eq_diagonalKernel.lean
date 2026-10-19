-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeBridge.momentCoverPartition_zero_eq_diagonalKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/fa23f582-77c5-4391-93d9-7b196f80055e

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
    exponentialPartition
        (momentHolomorphicBasisWeight
          K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p)
          (sourceTorusCoverPoint q))
        (momentTruncatedJetOrder K hk F htransport p N) 0 =
      diagonalKernel K k
        (momentNormalizedPotential F) q.1 := by
  unfold exponentialPartition exponentialMoment
  simp only [pow_zero, zero_mul, Real.exp_zero, mul_one]
  simpa [realLogCoordinate_sourceTorusCoverPoint] using
    (sum_momentHolomorphicBasisWeight_eq_diagonalKernel
      K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p)
        (sourceTorusCoverPoint q))
end Ehrhart.BergmanJetTorusRightSlopeBridge
