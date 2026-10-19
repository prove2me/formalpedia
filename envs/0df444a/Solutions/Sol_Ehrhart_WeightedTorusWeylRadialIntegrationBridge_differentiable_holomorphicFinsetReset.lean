-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.differentiable_holomorphicFinsetReset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/e1b0256f-8626-43b4-a9a9-67bea0a66f9c

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
    (hF : Differentiable ℂ F)
    (s : Finset (Fin n)) :
    Differentiable ℂ (holomorphicFinsetReset F s) := by
  unfold holomorphicFinsetReset
  change Differentiable ℂ
    (F ∘ fun w : TorusCharacters.LogSpace n =>
      fun i => if i ∈ s then 0 else w i)
  apply hF.comp
  apply differentiable_pi.mpr
  intro i
  by_cases hi : i ∈ s
  · simp [hi]
  · change Differentiable ℂ
      (fun w : TorusCharacters.LogSpace n =>
        if i ∈ s then 0 else w i)
    simp only [if_neg hi]
    exact (ContinuousLinearMap.proj i :
      TorusCharacters.LogSpace n →L[ℂ] ℂ).differentiable
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
