-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.differentiable_holomorphicCoordinateReset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/8bf794bd-2f12-4f88-8bb9-94021af95457

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusWeylRadialIntegrationBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ContDiff Convolution ENNReal Topology
open WeightedTorusWeylRepresentativeBridge
namespace Ehrhart.WeightedTorusWeylRadialIntegrationBridge
theorem _root_.solution {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F) (i : Fin n) :
    Differentiable ℂ (holomorphicCoordinateReset F i) := by
  unfold holomorphicCoordinateReset
  change Differentiable ℂ
    (F ∘ fun w : TorusCharacters.LogSpace n =>
      Function.update w i 0)
  apply hF.comp
  apply differentiable_pi.mpr
  intro j
  by_cases hj : j = i
  · subst j
    simp
  · have heq :
        (fun w : TorusCharacters.LogSpace n =>
          Function.update w i 0 j) =
          (fun w : TorusCharacters.LogSpace n => w j) := by
        funext w
        simp [hj]
    rw [heq]
    exact (ContinuousLinearMap.proj j :
      TorusCharacters.LogSpace n →L[ℂ] ℂ).differentiable
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
