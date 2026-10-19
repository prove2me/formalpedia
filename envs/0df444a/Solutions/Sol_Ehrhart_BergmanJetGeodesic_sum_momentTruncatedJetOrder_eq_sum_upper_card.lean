-- Prove2me | solution 1 for Ehrhart.BergmanJetGeodesic.sum_momentTruncatedJetOrder_eq_sum_upper_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/d9d89983-6f5d-4989-bec9-8862b5061494

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetGeodesic
open Set Function Filter MeasureTheory Module
open BergmanMonomials LatticeAsymptotics AdaptedBergmanBasis MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity BergmanJetBasis JetAdaptedOrthonormalBasis
open GenuineJetAdaptedBasisCounting
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace
  Topology
namespace Ehrhart.BergmanJetGeodesic
theorem _root_.solution
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ) :
    (∑ i : Fin (bergmanDimension K k),
      momentTruncatedJetOrder K hk F htransport p N i) =
      ∑ j ∈ Finset.range N,
        (momentUpperJetBasisIndices
          K hk F htransport p (j + 1)).card := by
  classical
  calc
    (∑ i : Fin (bergmanDimension K k),
      momentTruncatedJetOrder K hk F htransport p N i) =
      ∑ i : Fin (bergmanDimension K k),
        ∑ j ∈ Finset.range N,
          if momentSimultaneousJetBasis
            K hk F htransport p i ∈
            momentJetFiltration K hk F htransport p (j + 1)
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.card_filter _ _
    _ = ∑ j ∈ Finset.range N,
      ∑ i : Fin (bergmanDimension K k),
        if momentSimultaneousJetBasis
          K hk F htransport p i ∈
          momentJetFiltration K hk F htransport p (j + 1)
        then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range N,
      (momentUpperJetBasisIndices
        K hk F htransport p (j + 1)).card := by
      apply Finset.sum_congr rfl
      intro j _
      change
        (∑ i : Fin (bergmanDimension K k),
          if momentSimultaneousJetBasis
            K hk F htransport p i ∈
            momentJetFiltration K hk F htransport p (j + 1)
          then 1 else 0) =
          (Finset.univ.filter
            (fun i : Fin (bergmanDimension K k) =>
              momentSimultaneousJetBasis
                K hk F htransport p i ∈
                momentJetFiltration
                  K hk F htransport p (j + 1))).card
      exact (Finset.card_filter
        (fun i : Fin (bergmanDimension K k) =>
          momentSimultaneousJetBasis K hk F htransport p i ∈
            momentJetFiltration
              K hk F htransport p (j + 1)) Finset.univ).symm
end Ehrhart.BergmanJetGeodesic
