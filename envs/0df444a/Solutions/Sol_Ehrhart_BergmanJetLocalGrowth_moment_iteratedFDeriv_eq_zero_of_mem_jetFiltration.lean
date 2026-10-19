-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalGrowth.moment_iteratedFDeriv_eq_zero_of_mem_jetFiltration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/d95c89cf-53f4-4702-8f2a-e0e458ec1110

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_LaurentJetMultiplicityBridge_sum_coordinateMultiplicity
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_moment_iteratedFDeriv_coordinate_eq_zero_of_mem_jetFiltration

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
    (r : ℕ)
    (hs : s ∈ momentJetFiltration
      K hk F htransport p (r + 1)) :
    iteratedFDeriv ℂ r
      (momentHolomorphicRepresentative K hk F htransport s) p = 0 := by
  classical
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear
    (fun _ : Fin r => Pi.basisFun ℂ (Fin n))
  intro q
  simp only [Pi.basisFun_apply]
  exact moment_iteratedFDeriv_coordinate_eq_zero_of_mem_jetFiltration
    K hk F htransport p s q (coordinateMultiplicity q)
      (sum_coordinateMultiplicity q) (fun _ => rfl) hs
end Ehrhart.BergmanJetLocalGrowth
