-- Prove2me | solution 1 for Ehrhart.BergmanJetTriangularLatticeConvergence.triangularUnitLatticeStep_eq_tag_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/1b58887c-48c0-47ad-9239-44767b210a60

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
    (hB : BoxIntegral.hasIntegralVertices B)
    (s : Set (Space n))
    (G : ℕ → Space n → ℝ)
    (k : ℕ) (x : Space n)
    (hx : x ∈ (B : Set (Space n))) :
    triangularUnitLatticeStep B s G k x =
      s.indicator (G (k + 1))
        (BoxIntegral.unitPartition.tag (k + 1)
          (BoxIntegral.unitPartition.index (k + 1) x)) := by
  classical
  let ν : Fin n → ℤ := BoxIntegral.unitPartition.index (k + 1) x
  let J : BoxIntegral.Box (Fin n) :=
    BoxIntegral.unitPartition.box (k + 1) ν
  have hν : ν ∈ BoxIntegral.unitPartition.admissibleIndex (k + 1) B :=
    BoxIntegral.unitPartition.mem_admissibleIndex_of_mem_box
      (k + 1) hB hx
  have hJ : J ∈
      (BoxIntegral.unitPartition.prepartition (k + 1) B).boxes :=
    BoxIntegral.unitPartition.mem_prepartition_boxes_iff.mpr
      ⟨ν, hν, rfl⟩
  have hxJ : x ∈ (J : Set (Space n)) := by
    exact BoxIntegral.unitPartition.mem_box_iff_index.mpr rfl
  unfold triangularUnitLatticeStep
  rw [Finset.sum_eq_single J]
  · rw [Set.indicator_of_mem hxJ]
    rw [BoxIntegral.unitPartition.prepartition_tag (k + 1) hν]
  · intro I hI hne
    apply Set.indicator_of_notMem
    intro hxI
    apply hne
    exact (BoxIntegral.unitPartition.prepartition (k + 1) B)
      |>.toPrepartition.eq_of_mem_of_mem hI hJ hxI hxJ
  · intro hnot
    exact (hnot hJ).elim
end Ehrhart.BergmanJetTriangularLatticeConvergence
