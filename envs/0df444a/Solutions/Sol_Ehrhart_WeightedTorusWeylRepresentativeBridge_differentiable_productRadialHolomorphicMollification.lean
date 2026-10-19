-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRepresentativeBridge.differentiable_productRadialHolomorphicMollification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/0ffa8c37-93b6-4335-a8a2-ff6c0b607298

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultRegularity_differentiable_complex_of_weak_barPartial_convolution
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_contDiff_normalizedProductRadialKernel
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_hasCompactSupport_normalizedProductRadialKernel

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
theorem _root_.solution
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hweak : (∀ weakTest, ContDiff ℝ 1 weakTest → HasCompactSupport weakTest →
      ∀ weakCoordinate,
        (∫ weakPoint, g weakPoint *
          coverBarPartialTest weakTest weakCoordinate weakPoint) = 0)) :
    Differentiable ℂ (productRadialHolomorphicMollification g) := by
  unfold productRadialHolomorphicMollification
  rw [← complex_convolution_flip]
  apply differentiable_complex_of_weak_barPartial_convolution hg
  · exact (contDiff_normalizedProductRadialKernel n).of_le (by simp)
  · exact hasCompactSupport_normalizedProductRadialKernel n
  · exact hweak
end Ehrhart.WeightedTorusWeylRepresentativeBridge
