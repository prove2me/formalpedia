-- Prove2me | solution 1 for Ehrhart.BergmanJetGeodesic.sum_momentJetFiltration_finrank_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/387c3b41-59e1-4792-851a-7ab31634ba6d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetBasis_momentJetFiltration_finrank_ge

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
    (∑ j ∈ Finset.range N,
      (bergmanDimension K k - (n + j).choose n)) ≤
      ∑ j ∈ Finset.range N,
        Module.finrank ℂ
          (momentJetFiltration
            K hk F htransport p (j + 1)) := by
  apply Finset.sum_le_sum
  intro j _
  simpa using momentJetFiltration_finrank_ge
    K hk F htransport p (Nat.zero_lt_succ j)
end Ehrhart.BergmanJetGeodesic
