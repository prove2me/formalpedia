-- Prove2me | solution 1 for Ehrhart.WeightedTorusGraphWeakBridge.exists_integer_angularFundamentalBox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/2a2b1a44-a2ec-474e-82ec-ba76595caab3

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusGraphWeakBridge
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge
open WeightedTorusDistributionBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
namespace Ehrhart.WeightedTorusGraphWeakBridge
theorem _root_.solution {n : ℕ}
    (t : Space n) :
    ∃ q : Fin n → ℤ,
      t ∈ angularFundamentalBox (fun i => (q i : ℝ)) := by
  refine ⟨fun i => ⌈t i⌉ - 1, ?_⟩
  intro i
  constructor
  · push_cast
    have h := Int.ceil_lt_add_one (t i)
    linarith
  · push_cast
    have h := Int.le_ceil (t i)
    linarith
end Ehrhart.WeightedTorusGraphWeakBridge
