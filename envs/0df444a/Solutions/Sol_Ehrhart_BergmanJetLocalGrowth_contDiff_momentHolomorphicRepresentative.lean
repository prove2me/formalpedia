-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalGrowth.contDiff_momentHolomorphicRepresentative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/84014e91-4a2c-459b-9511-6da66fcb7cf7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_analyticAt_momentHolomorphicRepresentative

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetLocalGrowth
open Set Function Filter MeasureTheory Module Metric Asymptotics
open BergmanMonomials BergmanDiagonalBasisIndependence GlobalBergmanKernelBound AdaptedBergmanBasis
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open BergmanJetBasis MomentWeakGlobalKernel BergmanJetGeodesic BergmanJetProfileBridge
open BergmanJetRealGeodesic JetEnvelopeLocalGrowth LaurentJetMultiplicityBridge
open scoped BigOperators Topology ENNReal InnerProductSpace
namespace Ehrhart.BergmanJetLocalGrowth
theorem _root_.solution
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (s : momentMonomialSpan K hk F htransport) :
    ContDiff ℂ ⊤
      (momentHolomorphicRepresentative K hk F htransport s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (analyticAt_momentHolomorphicRepresentative
    K hk F htransport s p).contDiffAt
end Ehrhart.BergmanJetLocalGrowth
