-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRepresentativeBridge.hasCompactSupport_normalizedProductRadialKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/af38bc94-c30c-4786-890e-4674619775df

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_support_productRadialKernel_subset_closedBall

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusWeylRepresentativeBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ContDiff Convolution ENNReal Topology
open DolbeaultRegularity DolbeaultGraphDistributionBridge
namespace Ehrhart.WeightedTorusWeylRepresentativeBridge
theorem _root_.solution (n : ℕ) :
    HasCompactSupport
      (normalizedProductRadialKernel (n := n)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall
      (0 : TorusCharacters.LogSpace n) 1)
  intro w hw
  apply support_productRadialKernel_subset_closedBall n
  intro hzero
  apply hw
  simp [normalizedProductRadialKernel, hzero]
end Ehrhart.WeightedTorusWeylRepresentativeBridge
