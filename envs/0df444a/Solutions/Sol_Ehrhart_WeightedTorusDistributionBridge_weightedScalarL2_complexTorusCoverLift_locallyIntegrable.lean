-- Prove2me | solution 1 for Ehrhart.WeightedTorusDistributionBridge.weightedScalarL2_complexTorusCoverLift_locallyIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/c07264ba-5347-47d0-bb54-6da5028a0ef7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_weightedScalarL2_locallyIntegrable_unweighted

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
theorem _root_.solution
    {n k : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    (f : WeightedTorusHilbert.weightedHilbert k φ) :
    LocallyIntegrable
      (complexTorusCoverLift
        (fun z : WeightedTorusHilbert.LogTorus n => f z))
      (volume : Measure (TorusCharacters.LogSpace n)) :=
  complexTorusCoverLift_locallyIntegrable
    (weightedScalarL2_locallyIntegrable_unweighted hφ f)
end Ehrhart.WeightedTorusDistributionBridge
