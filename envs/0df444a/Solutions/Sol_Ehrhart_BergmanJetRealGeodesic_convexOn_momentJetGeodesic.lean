-- Prove2me | solution 1 for Ehrhart.BergmanJetRealGeodesic.convexOn_momentJetGeodesic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/4136672e-f0c4-4b62-b4d0-1fbd4de72b1d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanGeodesicConvexity_convexOn_logarithmicPotential

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetRealGeodesic
open Set Function Filter MeasureTheory Module
open BergmanMonomials MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity
open MomentWeakGlobalKernel BergmanJetGeodesic BergmanJetProfileBridge BergmanGeodesicConvexity
open BergmanDiagonalBasisIndependence
open scoped BigOperators ENNReal InnerProductSpace Topology
namespace Ehrhart.BergmanJetRealGeodesic
theorem _root_.solution
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (z : TorusCharacters.LogSpace n) :
    ConvexOn ℝ Set.univ
      (momentJetGeodesic K hk F htransport p N z) := by
  unfold momentJetGeodesic
  apply convexOn_logarithmicPotential
  · exact momentHolomorphicBasisWeight_nonneg
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  · exact exists_positive_momentHolomorphicBasisWeight
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  · exact_mod_cast hk
end Ehrhart.BergmanJetRealGeodesic
