-- Prove2me | solution 1 for Ehrhart.WeightedTorusDistributionBridge.weightedScalarL2_locallyIntegrable_weighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/4add99fc-8a61-482c-96b2-50c811c3bfff

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_weightedTorusMeasure_isLocallyFinite

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
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (f : WeightedTorusHilbert.weightedHilbert k φ) :
    LocallyIntegrable
      (fun z : WeightedTorusHilbert.LogTorus n => f z)
      (WeightedTorusHilbert.weightedTorusMeasure k φ) := by
  let : IsLocallyFiniteMeasure
      (WeightedTorusHilbert.weightedTorusMeasure k φ) :=
    weightedTorusMeasure_isLocallyFinite hφ
  exact (MeasureTheory.Lp.memLp f).locallyIntegrable (by norm_num)
end Ehrhart.WeightedTorusDistributionBridge
