-- Prove2me | solution 1 for Ehrhart.WeightedTorusDistributionBridge.weightedTorusMeasure_isLocallyFinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/6b60102b-0139-4ce2-91fa-eba88542c0de

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_weightedTorusMeasure_eq_unweighted_withDensity
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_continuous_realRadialWeight

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
    IsLocallyFiniteMeasure
      (WeightedTorusHilbert.weightedTorusMeasure k φ) := by
  let : IsLocallyFiniteMeasure (unweightedTorusMeasure n) :=
    unweightedTorusMeasure_isLocallyFinite n
  rw [weightedTorusMeasure_eq_unweighted_withDensity hφ]
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    (continuous_realRadialWeight hφ)
end Ehrhart.WeightedTorusDistributionBridge
