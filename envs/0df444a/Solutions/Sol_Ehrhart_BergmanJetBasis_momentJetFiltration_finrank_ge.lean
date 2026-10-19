-- Prove2me | solution 1 for Ehrhart.BergmanJetBasis.momentJetFiltration_finrank_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/f3cbc84f-6e77-457f-ab41-703e0ffcb5ca

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetBasis_bergmanDimension_le_momentJetFiltration_add_jetCount

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
    bergmanDimension K k - (n + j - 1).choose n ≤
      Module.finrank ℂ
        (momentJetFiltration K hk F htransport p j) := by
  have h := bergmanDimension_le_momentJetFiltration_add_jetCount
    K hk F htransport p hj
  omega
end Ehrhart.BergmanJetBasis
