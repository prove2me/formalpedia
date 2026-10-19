-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.fderiv_binaryAngularPartitionSum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/b5e8fa6a-a3d6-4e29-84aa-c707abaf65e3

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_contDiff_binaryAngularPartitionSum
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_fderiv_binaryAngularPartitionSum_eq_zero_of_open

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerIdentity
open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerIdentity
theorem _root_.solution
    {n : ℕ} (t : Space n)
    (hzero : ∀ i : Fin n, 0 ≤ t i)
    (hone : ∀ i : Fin n, t i ≤ 1) :
    fderiv ℝ (binaryAngularPartitionSum n) t = 0 := by
  let U : Set (Space n) :=
    Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) 1)
  let Z : Set (Space n) :=
    {s | fderiv ℝ (binaryAngularPartitionSum n) s = 0}
  have hcont : Continuous
      (fderiv ℝ (binaryAngularPartitionSum n)) := by
    exact (contDiff_binaryAngularPartitionSum (n := n) (m := 1)).continuous_fderiv
      (by simp)
  have hclosed : IsClosed Z := by
    exact isClosed_eq hcont continuous_const
  have hsub : U ⊆ Z := by
    intro s hs
    exact fderiv_binaryAngularPartitionSum_eq_zero_of_open s
      (fun i => (hs i (Set.mem_univ i)).1)
      (fun i => (hs i (Set.mem_univ i)).2)
  have ht : t ∈ closure U := by
    rw [show closure U =
      Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1) by
        dsimp [U]
        rw [closure_pi_set]
        simp]
    intro i _
    exact ⟨hzero i, hone i⟩
  exact (closure_minimal hsub hclosed) ht
end Ehrhart.MatrixTorusBochnerIdentity
