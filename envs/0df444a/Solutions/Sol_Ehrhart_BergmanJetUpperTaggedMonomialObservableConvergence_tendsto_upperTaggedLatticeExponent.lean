-- Prove2me | solution 1 for Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence.tendsto_upperTaggedLatticeExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/b154fa61-2c47-4d90-a708-74cd1f7d0d43

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTriangularLatticeConvergence_tendsto_unitPartition_tag_index
import Theorems.Thm_Ehrhart_BergmanJetUpperTaggedMonomialObservableConvergence_upperTaggedLatticeExponent_eq_unitPartition_tag

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
    {n : ℕ} (u : Space n) :
    Tendsto (fun k : ℕ => upperTaggedLatticeExponent k u)
      atTop (𝓝 u) := by
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  have htag := tendsto_unitPartition_tag_index u
  simpa only [upperTaggedLatticeExponent_eq_unitPartition_tag] using htag
end Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence
