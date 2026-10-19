-- Prove2me | solution 1 for Ehrhart.TorusMollificationLocalL2Bounds.complexShrinkingBump_rOut_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/61c375d1-46b9-47f1-aeb9-834e00ad0ab7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusMollificationLocalL2Bounds
open Set Function Filter MeasureTheory
open TorusCharacters DolbeaultRegularity TorusWeakDolbeaultMollification
open TorusFriedrichsMollifierEstimates
open scoped BigOperators ENNReal Topology ContDiff Convolution
namespace Ehrhart.TorusMollificationLocalL2Bounds
theorem _root_.solution
    {n : ℕ} (k : ℕ) :
    (complexShrinkingBump (n := n) k).rOut ≤ 1 := by
  change 1 / ((k : ℝ) + 1) ≤ 1
  rw [div_le_iff₀ (by positivity)]
  norm_num
end Ehrhart.TorusMollificationLocalL2Bounds
