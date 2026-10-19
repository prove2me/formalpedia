-- Prove2me | solution 1 for Ehrhart.WeightedTorusDistributionBridge.angularFundamentalEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/c17d72d5-7c4f-464d-90f4-d6d95360e506

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
theorem _root_.solution {n : ℕ}
    (t : angularFundamentalCell n) :
    (angularFundamentalEquiv n).symm t =
      (fun i : Fin n => (t.1 i : UnitAddCircle)) := by
  rfl
end Ehrhart.WeightedTorusDistributionBridge
