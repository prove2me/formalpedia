-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeBridge.momentPositiveTorusJetSlope_le_cover_positive_secant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/8474c1b1-535c-4907-9fa8-64ed19fe4c78

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetRealGeodesic_convexOn_momentJetGeodesic
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_momentPositiveTorusJetSlope_eq_deriv_cover

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
    (p : LogSpace n) (N : ℕ) (q : LogTorus n)
    {t : ℝ} (ht : 0 < t) :
    momentPositiveTorusJetSlope
        K hk F htransport p N q ≤
      (momentJetGeodesic K hk F htransport p N
          (sourceTorusCoverPoint q) t -
        momentJetGeodesic K hk F htransport p N
          (sourceTorusCoverPoint q) 0) / t := by
  rw [momentPositiveTorusJetSlope_eq_deriv_cover]
  have hdiff :
      DifferentiableAt ℝ
        (momentJetGeodesic K hk F htransport p N
          (sourceTorusCoverPoint q)) 0 := by
    unfold momentJetGeodesic
    exact (hasDerivAt_logarithmicPotential
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
      (k : ℝ) 0).differentiableAt
  have h :=
    (convexOn_momentJetGeodesic
      K hk F htransport p N (sourceTorusCoverPoint q)).deriv_le_slope
        (Set.mem_univ (0 : ℝ)) (Set.mem_univ t) ht hdiff
  simpa [slope_def_field] using h
end Ehrhart.BergmanJetTorusRightSlopeBridge
