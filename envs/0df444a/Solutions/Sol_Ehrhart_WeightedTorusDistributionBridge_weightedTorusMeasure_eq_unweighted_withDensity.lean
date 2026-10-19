-- Prove2me | solution 1 for Ehrhart.WeightedTorusDistributionBridge.weightedTorusMeasure_eq_unweighted_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/221f7e07-7c4e-4763-97eb-d2872e27abdf

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
theorem _root_.solution {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    WeightedTorusHilbert.weightedTorusMeasure k φ =
      (unweightedTorusMeasure n).withDensity
        (fun z : WeightedTorusHilbert.LogTorus n =>
          WeightedTorusHilbert.radialWeight k φ z.1) := by
  exact WeightedTorusHilbert.weightedTorusMeasure_eq_withDensity
    k hφ
end Ehrhart.WeightedTorusDistributionBridge
