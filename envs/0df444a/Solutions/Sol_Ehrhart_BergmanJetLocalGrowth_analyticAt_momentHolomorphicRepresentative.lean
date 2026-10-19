-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalGrowth.analyticAt_momentHolomorphicRepresentative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/0037de63-7778-41f6-b2c6-9c4a9d14e3fa

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_LaurentJetSeparatedness_analyticAt_normalizedHolomorphicMonomial

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
    (s : momentMonomialSpan K hk F htransport)
    (p : TorusCharacters.LogSpace n) :
    AnalyticAt ℂ
      (momentHolomorphicRepresentative K hk F htransport s) p := by
  classical
  unfold momentHolomorphicRepresentative
  rw [LinearMap.comp_apply, Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  apply Finset.analyticAt_sum
  intro u _
  exact
    (LaurentJetSeparatedness.analyticAt_normalizedHolomorphicMonomial
      K hk (momentNormalizedPotential F) u p).const_smul
end Ehrhart.BergmanJetLocalGrowth
