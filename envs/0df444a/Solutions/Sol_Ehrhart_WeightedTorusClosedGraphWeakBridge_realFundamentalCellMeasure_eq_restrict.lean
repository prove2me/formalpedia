-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.realFundamentalCellMeasure_eq_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/93196d68-479a-4adb-a652-40b290b3b3b4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusClosedGraphWeakBridge
open Set Function MeasureTheory Filter
open WeightedTorusHilbert WeightedBrascampSaturation ComplexKillingSaturationBridge
open DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
  Manifold ContDiff
namespace Ehrhart.WeightedTorusClosedGraphWeakBridge
theorem _root_.solution {n : ℕ}
    (b : Space n) :
    realFundamentalCellMeasure b =
      (volume : Measure (Space n × Space n)).restrict
        (Set.univ ×ˢ angularFundamentalBox b) := by
  rw [Measure.volume_eq_prod]
  simpa [realFundamentalCellMeasure] using
    (MeasureTheory.Measure.prod_restrict
      (μ := (volume : Measure (Space n)))
      (ν := (volume : Measure (Space n)))
      (Set.univ : Set (Space n))
      (angularFundamentalBox b))
end Ehrhart.WeightedTorusClosedGraphWeakBridge
