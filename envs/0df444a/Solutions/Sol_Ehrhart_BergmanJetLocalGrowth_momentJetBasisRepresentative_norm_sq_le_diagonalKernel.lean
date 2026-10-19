-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalGrowth.momentJetBasisRepresentative_norm_sq_le_diagonalKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/c31b70de-ad16-4aef-a956-1c6c56448ec6

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    (p z : TorusCharacters.LogSpace n)
    (i : Fin (bergmanDimension K k)) :
    ‖momentHolomorphicRepresentative K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p i) z‖ ^ 2 ≤
      diagonalKernel K k (momentNormalizedPotential F)
        (realLogCoordinate z) := by
  have hsum := Finset.single_le_sum
    (fun j _ => momentHolomorphicBasisWeight_nonneg K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z j)
    (Finset.mem_univ i)
  rw [sum_momentHolomorphicBasisWeight_eq_diagonalKernel
    K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z] at hsum
  simpa [momentHolomorphicBasisWeight,
    Complex.normSq_eq_norm_sq] using hsum
end Ehrhart.BergmanJetLocalGrowth
