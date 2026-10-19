-- Prove2me | solution 1 for Ehrhart.BergmanJetBasis.bergmanDimension_le_momentJetFiltration_add_jetCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/d8d78670-2c9c-4a71-b77f-95c4aade65bc

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetCounting_finrank_le_kernel_add_jetCount

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetBasis
open Set Function Filter MeasureTheory Module
open BergmanMonomials LatticeAsymptotics WeightedTorusHilbert AdaptedBergmanBasis MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace
  Topology
namespace Ehrhart.BergmanJetBasis
theorem _root_.solution
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {j : ℕ} (hj : 0 < j) :
    bergmanDimension K k ≤
      Module.finrank ℂ (momentJetFiltration
        K hk F htransport p j) +
        (n + j - 1).choose n := by
  let := finiteDimensional_momentMonomialSpan
    K hk F htransport
  have h := JetCounting.finrank_le_kernel_add_jetCount ℂ
    (momentMonomialSpan K hk F htransport) n j hj
    (momentHolomorphicJetMap K hk F htransport p j)
  rw [← finrank_momentMonomialSpan K hk F htransport]
  exact h
end Ehrhart.BergmanJetBasis
