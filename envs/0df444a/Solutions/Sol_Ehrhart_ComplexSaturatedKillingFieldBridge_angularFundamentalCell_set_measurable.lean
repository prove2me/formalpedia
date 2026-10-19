-- Prove2me | solution 1 for Ehrhart.ComplexSaturatedKillingFieldBridge.angularFundamentalCell_set_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/1d23f449-a82b-488a-a20b-7d439e363c37

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.ComplexSaturatedKillingFieldBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ContDiff Convolution ENNReal InnerProductSpace Topology
open WeightedTorusHilbert WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open JointHolomorphicLaurentFourierCompatibility
namespace Ehrhart.ComplexSaturatedKillingFieldBridge
theorem _root_.solution (n : ℕ) :
    MeasurableSet
      {t : Space n |
        ∀ i : Fin n, t i ∈ Set.Ioc (0 : ℝ) ((0 : ℝ) + 1)} := by
  have hbox : MeasurableSet
      (angularFundamentalBox (0 : Space n)) := by
    unfold angularFundamentalBox
    exact MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)
  simpa [angularFundamentalBox, Set.pi] using hbox
end Ehrhart.ComplexSaturatedKillingFieldBridge
