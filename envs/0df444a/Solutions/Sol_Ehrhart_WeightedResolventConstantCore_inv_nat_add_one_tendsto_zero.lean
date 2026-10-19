-- Prove2me | solution 1 for Ehrhart.WeightedResolventConstantCore.inv_nat_add_one_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/1b7f2af8-4a4b-4f3d-9ba2-69f2e4e260d0

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
theorem _root_.solution :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹)
      atTop (nhds 0) := by
  have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcast
  simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
    hinv.comp (tendsto_add_atTop_nat 1)
end Ehrhart.WeightedResolventConstantCore
