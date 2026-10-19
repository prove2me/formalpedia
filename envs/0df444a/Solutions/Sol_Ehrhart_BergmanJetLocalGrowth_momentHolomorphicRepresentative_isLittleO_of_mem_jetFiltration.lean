-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalGrowth.momentHolomorphicRepresentative_isLittleO_of_mem_jetFiltration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/90a928e1-0c88-4df9-93f2-1b956a0d6a15

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_isLittleO_norm_pow_of_iteratedFDeriv_zero
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_contDiff_momentHolomorphicRepresentative
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_moment_iteratedFDeriv_eq_zero_of_mem_jetFiltration

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
    (j : ℕ)
    (hs : s ∈ momentJetFiltration
      K hk F htransport p (j + 1)) :
    (fun z : TorusCharacters.LogSpace n =>
      momentHolomorphicRepresentative K hk F htransport s z -
        momentHolomorphicRepresentative K hk F htransport s p)
      =o[𝓝 p]
        (fun z : TorusCharacters.LogSpace n => ‖z - p‖ ^ j) := by
  apply isLittleO_norm_pow_of_iteratedFDeriv_zero
    _ (contDiff_momentHolomorphicRepresentative
      K hk F htransport s) p j
  intro i hi
  apply moment_iteratedFDeriv_eq_zero_of_mem_jetFiltration
    K hk F htransport p s i
  exact momentJetFiltration_antitone
    K hk F htransport p (show i + 1 ≤ j + 1 by omega) hs
end Ehrhart.BergmanJetLocalGrowth
