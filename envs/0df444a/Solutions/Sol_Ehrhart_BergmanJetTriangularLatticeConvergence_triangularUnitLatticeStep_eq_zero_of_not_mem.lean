-- Prove2me | solution 1 for Ehrhart.BergmanJetTriangularLatticeConvergence.triangularUnitLatticeStep_eq_zero_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/2e538376-47ea-46bd-9920-0500726f746f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetTriangularLatticeConvergence
open Set Filter MeasureTheory Metric
open LatticeAsymptotics
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetTriangularLatticeConvergence
theorem _root_.solution {n : ℕ}
    (B : BoxIntegral.Box (Fin n))
    (s : Set (Space n))
    (G : ℕ → Space n → ℝ)
    (k : ℕ) (x : Space n)
    (hx : x ∉ (B : Set (Space n))) :
    triangularUnitLatticeStep B s G k x = 0 := by
  classical
  unfold triangularUnitLatticeStep
  apply Finset.sum_eq_zero
  intro J hJ
  apply Set.indicator_of_notMem
  intro hxJ
  apply hx
  exact ((BoxIntegral.unitPartition.prepartition (k + 1) B)
    |>.toPrepartition.le_of_mem hJ) hxJ
end Ehrhart.BergmanJetTriangularLatticeConvergence
