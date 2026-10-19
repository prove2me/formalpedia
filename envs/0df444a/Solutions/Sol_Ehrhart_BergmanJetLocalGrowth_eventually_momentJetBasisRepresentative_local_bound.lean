-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalGrowth.eventually_momentJetBasisRepresentative_local_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/188de6a0-e0b9-449a-b161-0cb822b8882a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_momentLocalCoverPotential_le_localMaximum
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_momentJetBasisRepresentative_norm_sq_le_diagonalKernel

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
      (i : Fin (bergmanDimension K k))
      (z : TorusCharacters.LogSpace n),
      z ∈ Metric.ball p R →
        ‖momentHolomorphicRepresentative K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p i) z‖ ≤
          Real.sqrt
            (Real.exp ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
              globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n)) := by
  filter_upwards
    [eventually_momentNormalized_diagonalKernel_le_polynomial
      K F htransport] with k hglobal hk i z hz
  have hpot : momentNormalizedPotential F (realLogCoordinate z) ≤
      momentLocalPotentialMaximum K F p R :=
    momentLocalCoverPotential_le_localMaximum K F p R z
      (Metric.ball_subset_closedBall hz)
  have hdiag := hglobal (realLogCoordinate z)
  have hdim := momentJetBasisRepresentative_norm_sq_le_diagonalKernel
    K hk F htransport p z i
  apply Real.le_sqrt_of_sq_le
  calc
    ‖momentHolomorphicRepresentative K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p i) z‖ ^ 2 ≤
      diagonalKernel K k (momentNormalizedPotential F)
        (realLogCoordinate z) := hdim
    _ ≤ Real.exp ((k : ℝ) *
          momentNormalizedPotential F (realLogCoordinate z)) *
            globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n) := hdiag
    _ ≤ Real.exp ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
          globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n) := by
      gcongr
      exact (globalKernelPolynomialConstant_pos K).le
end Ehrhart.BergmanJetLocalGrowth
