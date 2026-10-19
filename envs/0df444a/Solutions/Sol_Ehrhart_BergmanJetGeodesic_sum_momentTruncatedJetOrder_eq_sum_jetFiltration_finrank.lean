-- Prove2me | solution 1 for Ehrhart.BergmanJetGeodesic.sum_momentTruncatedJetOrder_eq_sum_jetFiltration_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/b5fe2180-dcd7-4e59-8dc1-2d29dba45aa8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetGeodesic_card_momentUpperJetBasisIndices_eq_finrank
import Theorems.Thm_Ehrhart_BergmanJetGeodesic_sum_momentTruncatedJetOrder_eq_sum_upper_card

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
        Module.finrank ℂ
          (momentJetFiltration
            K hk F htransport p (j + 1)) := by
  rw [sum_momentTruncatedJetOrder_eq_sum_upper_card]
  apply Finset.sum_congr rfl
  intro j _
  exact card_momentUpperJetBasisIndices_eq_finrank
    K hk F htransport p (j + 1)
end Ehrhart.BergmanJetGeodesic
