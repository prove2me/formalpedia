-- Prove2me | solution 1 for Ehrhart.WeightedTorusGraphWeakBridge.integer_angularFundamentalBoxes_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/1d2db6ee-0521-44a7-89df-210e1e1b6b96

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusGraphWeakBridge_exists_integer_angularFundamentalBox

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
theorem _root_.solution (n : ℕ) :
    (⋃ q : Fin n → ℤ,
      (Set.univ : Set (Space n)) ×ˢ
        angularFundamentalBox (fun i => (q i : ℝ))) =
      (Set.univ : Set (Space n × Space n)) := by
  apply Set.iUnion_eq_univ_iff.mpr
  intro p
  obtain ⟨q, hq⟩ := exists_integer_angularFundamentalBox p.2
  exact ⟨q, ⟨Set.mem_univ p.1, hq⟩⟩
end Ehrhart.WeightedTorusGraphWeakBridge
