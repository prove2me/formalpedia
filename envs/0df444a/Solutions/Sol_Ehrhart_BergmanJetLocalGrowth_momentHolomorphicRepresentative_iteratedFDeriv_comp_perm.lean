-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalGrowth.momentHolomorphicRepresentative_iteratedFDeriv_comp_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/4c822694-4639-49d3-bf6a-b012609a833a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_contDiff_momentHolomorphicRepresentative

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
    (p : TorusCharacters.LogSpace n)
    (s : momentMonomialSpan K hk F htransport)
    {r : ℕ} (v : Fin r → TorusCharacters.LogSpace n)
    (σ : Equiv.Perm (Fin r)) :
    (iteratedFDeriv ℂ r
      (momentHolomorphicRepresentative K hk F htransport s) p)
        (v ∘ σ) =
    (iteratedFDeriv ℂ r
      (momentHolomorphicRepresentative K hk F htransport s) p) v := by
  exact (contDiff_momentHolomorphicRepresentative
    K hk F htransport s).contDiffAt.iteratedFDeriv_comp_perm v σ
end Ehrhart.BergmanJetLocalGrowth
