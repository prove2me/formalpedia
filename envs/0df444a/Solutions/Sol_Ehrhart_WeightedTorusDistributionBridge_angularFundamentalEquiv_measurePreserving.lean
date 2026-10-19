-- Prove2me | solution 1 for Ehrhart.WeightedTorusDistributionBridge.angularFundamentalEquiv_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/1a94be4b-819c-4a37-8ed0-32c2a3c61422

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
    MeasurePreserving (angularFundamentalEquiv n)
      (WeightedTorusHilbert.angularMeasure n)
      (angularFundamentalMeasure n) := by
  simpa [angularFundamentalEquiv, angularFundamentalMeasure,
    WeightedTorusHilbert.angularMeasure] using
    (UnitAddTorus.measurePreserving_equivPiIoc
      (fun _ : Fin n => (0 : ℝ)))
end Ehrhart.WeightedTorusDistributionBridge
