-- Prove2me | solution 1 for Ehrhart.BergmanJetGeodesic.real_jetLayercake_le_sum_momentTruncatedJetOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/1da68937-19aa-4322-9cf8-8c2ddebae126

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetFiltration_real_jetLayercake_le_nat_sum
import Theorems.Thm_Ehrhart_BergmanJetGeodesic_sum_momentTruncatedJetOrder_eq_sum_jetFiltration_finrank
import Theorems.Thm_Ehrhart_BergmanJetGeodesic_sum_momentJetFiltration_finrank_ge

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
    (N : ℝ) * (bergmanDimension K k : ℝ) -
      (((n + N).choose (n + 1) : ℕ) : ℝ) ≤
        ((∑ i : Fin (bergmanDimension K k),
          momentTruncatedJetOrder
            K hk F htransport p N i) : ℝ) := by
  calc
    (N : ℝ) * (bergmanDimension K k : ℝ) -
        (((n + N).choose (n + 1) : ℕ) : ℝ) ≤
      ((∑ j ∈ Finset.range N,
        (bergmanDimension K k - (n + j).choose n) : ℕ) : ℝ) :=
        BergmanJetFiltration.real_jetLayercake_le_nat_sum
          n (bergmanDimension K k) N
    _ ≤ ((∑ j ∈ Finset.range N,
          Module.finrank ℂ
            (momentJetFiltration
              K hk F htransport p (j + 1)) : ℕ) : ℝ) := by
      exact_mod_cast sum_momentJetFiltration_finrank_ge
        K hk F htransport p N
    _ = ((∑ i : Fin (bergmanDimension K k),
          momentTruncatedJetOrder
            K hk F htransport p N i) : ℝ) := by
      exact_mod_cast
        (sum_momentTruncatedJetOrder_eq_sum_jetFiltration_finrank
          K hk F htransport p N).symm
end Ehrhart.BergmanJetGeodesic
