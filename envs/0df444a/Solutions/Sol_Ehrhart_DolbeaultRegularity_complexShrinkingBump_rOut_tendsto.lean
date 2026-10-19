-- Prove2me | solution 1 for Ehrhart.DolbeaultRegularity.complexShrinkingBump_rOut_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/3a58276f-f903-407e-afc6-5cfa7312b5a4

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
theorem _root_.solution {n : ℕ} :
    Tendsto (fun k : ℕ => (complexShrinkingBump (n := n) k).rOut)
      Filter.atTop (nhds 0) := by
  simpa [complexShrinkingBump] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
end Ehrhart.DolbeaultRegularity
