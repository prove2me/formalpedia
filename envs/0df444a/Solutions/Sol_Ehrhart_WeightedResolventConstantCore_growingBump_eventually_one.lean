-- Prove2me | solution 1 for Ehrhart.WeightedResolventConstantCore.growingBump_eventually_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/375e9d81-ab31-4f35-9d00-e257e7cd78bd

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedResolventConstantCore
open Set Function MeasureTheory Filter Matrix
open WeightedPoincare WeightedBrascampLieb
open scoped BigOperators ENNReal InnerProductSpace Topology
namespace Ehrhart.WeightedResolventConstantCore
theorem _root_.solution {n : ℕ} (x : Space n) :
    ∀ᶠ k : ℕ in atTop, growingBump k x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop N] with k hk
  apply (growingBump k).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖x‖ ≤ (k : ℝ) + 1
  have hNk : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  linarith
end Ehrhart.WeightedResolventConstantCore
