-- Prove2me | solution 1 for Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence.unitPartition_tag_index_mem_scaledIntegerLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/9e3c5775-5fda-4b66-b4eb-5640c1121be7

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
    {n : ℕ} (k : ℕ) (u : Space n) :
    BoxIntegral.unitPartition.tag (k + 1)
        (BoxIntegral.unitPartition.index (k + 1) u) ∈
      scaledIntegerLattice n (k + 1) := by
  rw [scaledIntegerLattice, ← Submodule.coe_pointwise_smul]
  exact BoxIntegral.unitPartition.tag_mem_smul_span
    (n := k + 1)
    (BoxIntegral.unitPartition.index (k + 1) u)
end Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence
