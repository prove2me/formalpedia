-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.angularSmoothPartition_binary_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/3276b0de-4e12-4577-b60d-b36e5484420e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_angularSmoothPartitionBump_add_translate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerBridge
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerBridge
theorem _root_.solution
    {n : ℕ} (t : Space n)
    (hzero : ∀ i : Fin n, 0 ≤ t i)
    (hone : ∀ i : Fin n, t i ≤ 1) :
    (∑ q : Fin n → Bool,
      angularSmoothPartition
        (fun i => t i - if q i then (1 : ℝ) else 0)) = 1 := by
  classical
  calc
    _ = ∑ q : Fin n → Bool,
      ∏ i : Fin n,
        angularSmoothPartitionBump
          (t i - if q i then (1 : ℝ) else 0) := rfl
    _ = ∏ i : Fin n, ∑ b : Bool,
      angularSmoothPartitionBump
        (t i - if b then (1 : ℝ) else 0) :=
      (Fintype.prod_sum
        (fun (i : Fin n) (b : Bool) =>
          angularSmoothPartitionBump
            (t i - if b then (1 : ℝ) else 0))).symm
    _ = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simpa [add_comm] using
        angularSmoothPartitionBump_add_translate
          (hzero i) (hone i)
end Ehrhart.MatrixTorusBochnerBridge
