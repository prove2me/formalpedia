-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalGrowth.eventually_momentJetBasisRepresentative_local_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/bdcd4f75-ee0a-4df5-8aa4-684e18f3f2e4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_momentSimultaneousJetBasis_mem_truncatedJetFiltration
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_momentHolomorphicRepresentative_schwarz_of_mem_jetFiltration
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_eventually_momentJetBasisRepresentative_local_bound

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
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (R : ℝ) :
    ∀ᶠ k : ℕ in atTop, ∀ (hk : 0 < k)
      (N : ℕ) (i : Fin (bergmanDimension K k))
      (z : TorusCharacters.LogSpace n),
      z ∈ Metric.ball p R →
        ‖momentHolomorphicRepresentative K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p i) z‖ ≤
          Real.sqrt
            (Real.exp ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
              globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n)) *
            (dist z p / R) ^
              momentTruncatedJetOrder K hk F htransport p N i := by
  filter_upwards
    [eventually_momentJetBasisRepresentative_local_bound
      K F htransport p R] with k hbound hk N i z hz
  exact momentHolomorphicRepresentative_schwarz_of_mem_jetFiltration
    K hk F htransport p
      (momentSimultaneousJetBasis K hk F htransport p i)
      (momentTruncatedJetOrder K hk F htransport p N i)
      (momentSimultaneousJetBasis_mem_truncatedJetFiltration
        K hk F htransport p N i)
      R _ (fun w hw => hbound hk i w hw) z hz
end Ehrhart.BergmanJetLocalGrowth
