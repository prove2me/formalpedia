-- Prove2me | solution 1 for Ehrhart.WeightedTorusDistributionBridge.unweightedTorusFundamental_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/8a79c17f-1ef4-4c05-88ad-d43e21988d60

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_angularFundamentalEquiv_measurePreserving

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
    MeasurePreserving (torusFundamentalMeasurableEquiv n)
      (unweightedTorusMeasure n)
      (unweightedFundamentalMeasure n) := by
  change MeasurePreserving
    (Prod.map id (angularFundamentalEquiv n))
    ((volume : Measure (Space n)).prod
      (WeightedTorusHilbert.angularMeasure n))
    ((volume : Measure (Space n)).prod
      (angularFundamentalMeasure n))
  exact (MeasurePreserving.id
    (volume : Measure (Space n))).prod
      (angularFundamentalEquiv_measurePreserving n)
end Ehrhart.WeightedTorusDistributionBridge
