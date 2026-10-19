-- Prove2me | solution 1 for Ehrhart.DolbeaultRegularity.complexShrinkingBump_radius_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/667d01c1-4fcf-4525-8dc5-d7af98ef9ea0

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.DolbeaultRegularity
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
namespace Ehrhart.DolbeaultRegularity
theorem _root_.solution {n : ℕ} (k : ℕ) :
    (complexShrinkingBump (n := n) k).rOut ≤
      2 * (complexShrinkingBump (n := n) k).rIn := by
  dsimp [complexShrinkingBump]
  ring_nf
  exact le_rfl
end Ehrhart.DolbeaultRegularity
