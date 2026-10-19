-- Prove2me | solution 1 for Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence.upperTaggedLatticeExponent_eq_unitPartition_tag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/1cd2b9a9-8fe8-4e30-b8bf-3c0104f435fc

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence
open Set Function Filter MeasureTheory
open LaplaceAsymptotics LatticeAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open BergmanJetDualGradientConcentration BergmanJetMovingMonomialObservableConvergence
open BergmanJetRoundedMonomialObservableConvergence BergmanJetTriangularLatticeConvergence
open BergmanJetDiagonalObservableLatticeIdentity
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence
theorem _root_.solution
    {n k : ℕ} [NeZero k]
    (u : Space n) :
    upperTaggedLatticeExponent k u =
      BoxIntegral.unitPartition.tag k
        (BoxIntegral.unitPartition.index k u) := by
  funext i
  simp [upperTaggedLatticeExponent,
    BoxIntegral.unitPartition.tag,
    BoxIntegral.unitPartition.index]
end Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence
