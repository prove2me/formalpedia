-- Prove2me | solution 1 for Ehrhart.WeightedTorusDistributionBridge.logarithmicCoordinates_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/5c531ce4-b013-4b46-9759-7121680f2333

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusDistributionBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
attribute [local instance] Ehrhart.WeightedTorusDistributionBridge._p2m_local_instance_3610026555_18903
attribute [local instance] Ehrhart.WeightedTorusDistributionBridge._p2m_local_instance_3610026555_18906
namespace Ehrhart.WeightedTorusDistributionBridge
theorem _root_.solution (n : ℕ) :
    MeasurePreserving (logarithmicCoordinatesEquiv n)
      (volume : Measure (Space n × Space n))
      (logarithmicCoverPushforward n) := by
  exact (logarithmicCoordinatesEquiv n).toHomeomorph.measurable.measurePreserving
      (volume : Measure (Space n × Space n))
end Ehrhart.WeightedTorusDistributionBridge
