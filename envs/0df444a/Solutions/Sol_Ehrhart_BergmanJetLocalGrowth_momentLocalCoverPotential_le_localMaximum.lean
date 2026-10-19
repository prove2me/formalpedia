-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalGrowth.momentLocalCoverPotential_le_localMaximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/611f5672-deed-4e29-9b3a-96fb22d3f357

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_momentLocalPotential_image_bddAbove

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
    (p : TorusCharacters.LogSpace n) (R : ℝ)
    (z : TorusCharacters.LogSpace n)
    (hz : z ∈ Metric.closedBall p R) :
    momentLocalCoverPotential K F z ≤
      momentLocalPotentialMaximum K F p R := by
  apply le_csSup (momentLocalPotential_image_bddAbove K F p R)
  exact ⟨z, hz, rfl⟩
end Ehrhart.BergmanJetLocalGrowth
