-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.fderiv_binaryAngularPartitionSum_eq_zero_of_open
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/fe073dab-2739-4e21-b8ca-eeaa8f7c900b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_binaryAngularPartitionSum_eq_one

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
    (hzero : ∀ i : Fin n, 0 < t i)
    (hone : ∀ i : Fin n, t i < 1) :
    fderiv ℝ (binaryAngularPartitionSum n) t = 0 := by
  let U : Set (Space n) :=
    Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) 1)
  have hU : IsOpen U :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have ht : t ∈ U := by
    intro i _
    exact ⟨hzero i, hone i⟩
  have hevent :
      binaryAngularPartitionSum n =ᶠ[𝓝 t]
        (fun _ : Space n => (1 : ℝ)) := by
    filter_upwards [hU.mem_nhds ht] with s hs
    exact binaryAngularPartitionSum_eq_one s
      (fun i => (hs i (Set.mem_univ i)).1.le)
      (fun i => (hs i (Set.mem_univ i)).2.le)
  simpa using (hevent.fderiv_eq (𝕜 := ℝ))
end Ehrhart.MatrixTorusBochnerIdentity
