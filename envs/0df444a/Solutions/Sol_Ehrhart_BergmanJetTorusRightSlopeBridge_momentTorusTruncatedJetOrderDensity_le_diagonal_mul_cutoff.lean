-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeBridge.momentTorusTruncatedJetOrderDensity_le_diagonal_mul_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/a8b34492-7a74-47d7-a7bb-e88e94fc92b6

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
    momentTorusTruncatedJetOrderDensity
      K hk F htransport p N q ≤
        (N : ℝ) * diagonalKernel K k
          (momentNormalizedPotential F) q.1 := by
  have hdiag :
      (∑ i : Fin (bergmanDimension K k),
        momentTorusJetBasisWeight
          K hk F htransport p q i) =
        diagonalKernel K k
          (momentNormalizedPotential F) q.1 := by
    simpa [momentTorusJetBasisWeight] using
      (sum_momentTorusRepresentative_normSq_eq_diagonalKernel
        K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p) q)
  calc
    momentTorusTruncatedJetOrderDensity
        K hk F htransport p N q ≤
      ∑ i : Fin (bergmanDimension K k),
        (N : ℝ) * momentTorusJetBasisWeight
          K hk F htransport p q i := by
      unfold momentTorusTruncatedJetOrderDensity
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast
          momentTruncatedJetOrder_le
            K hk F htransport p N i
      · exact Complex.normSq_nonneg _
    _ = (N : ℝ) *
        (∑ i : Fin (bergmanDimension K k),
          momentTorusJetBasisWeight
            K hk F htransport p q i) := by
      rw [Finset.mul_sum]
    _ = (N : ℝ) * diagonalKernel K k
          (momentNormalizedPotential F) q.1 := by
      rw [hdiag]
end Ehrhart.BergmanJetTorusRightSlopeBridge
