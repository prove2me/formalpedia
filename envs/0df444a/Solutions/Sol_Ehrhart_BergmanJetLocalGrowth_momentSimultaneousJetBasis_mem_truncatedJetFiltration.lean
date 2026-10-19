-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalGrowth.momentSimultaneousJetBasis_mem_truncatedJetFiltration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/494101a1-84f6-41bf-82e7-7200fc6c38e5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetGeodesic_momentJetFiltration_zero

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
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (i : Fin (bergmanDimension K k)) :
    momentSimultaneousJetBasis K hk F htransport p i ∈
      momentJetFiltration K hk F htransport p
        (momentTruncatedJetOrder K hk F htransport p N i) := by
  classical
  let S : Finset ℕ := (Finset.range N).filter (fun j =>
    momentSimultaneousJetBasis K hk F htransport p i ∈
      momentJetFiltration K hk F htransport p (j + 1))
  change momentSimultaneousJetBasis K hk F htransport p i ∈
    momentJetFiltration K hk F htransport p S.card
  by_cases hzero : S.card = 0
  · rw [hzero, momentJetFiltration_zero]
    simp
  · have hpos : 0 < S.card := Nat.pos_of_ne_zero hzero
    by_contra hnot
    have hsub : S ⊆ Finset.range (S.card - 1) := by
      intro j hj
      have hmem :
          momentSimultaneousJetBasis K hk F htransport p i ∈
            momentJetFiltration K hk F htransport p (j + 1) :=
        (Finset.mem_filter.mp hj).2
      apply Finset.mem_range.mpr
      by_contra hlt
      have hle : S.card ≤ j + 1 := by omega
      exact hnot
        (momentJetFiltration_antitone
          K hk F htransport p hle hmem)
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_range] at hcard
    omega
end Ehrhart.BergmanJetLocalGrowth
