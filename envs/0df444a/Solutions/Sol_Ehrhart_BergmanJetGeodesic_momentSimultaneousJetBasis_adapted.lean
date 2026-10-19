-- Prove2me | solution 1 for Ehrhart.BergmanJetGeodesic.momentSimultaneousJetBasis_adapted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/d7108dd4-c6d8-4905-a77b-e0eb49b9d633

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
    (p : TorusCharacters.LogSpace n)
    (j : ℕ) (i : Fin (bergmanDimension K k)) :
    momentSimultaneousJetBasis K hk F htransport p i ∈
        momentJetFiltration K hk F htransport p j ∨
      momentSimultaneousJetBasis K hk F htransport p i ∈
        (momentJetFiltration K hk F htransport p j)ᗮ :=
  Classical.choose_spec
    (exists_momentSimultaneousJetBasis K hk F htransport p) j i
end Ehrhart.BergmanJetGeodesic
