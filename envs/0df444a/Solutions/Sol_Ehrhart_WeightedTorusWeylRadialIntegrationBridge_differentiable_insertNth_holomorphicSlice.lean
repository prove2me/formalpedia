-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.differentiable_insertNth_holomorphicSlice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/be1fc310-9138-471e-ab32-16a2195ee67e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_HolomorphicLaurentFourierCompletenessBridge_differentiable_coordinateHolomorphicSlice

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
    {F : TorusCharacters.LogSpace (n + 1) → ℂ}
    (hF : Differentiable ℂ F)
    (i : Fin (n + 1))
    (y : TorusCharacters.LogSpace n) :
    Differentiable ℂ
      (fun x : ℂ => F (i.insertNth x y)) := by
  have hslice :=
    HolomorphicLaurentFourierCompletenessBridge.differentiable_coordinateHolomorphicSlice
      hF (i.insertNth (0 : ℂ) y) i
  have heq :
      (fun x : ℂ => F (i.insertNth x y)) =
        HolomorphicLaurentFourierCompletenessBridge.coordinateHolomorphicSlice
          F (i.insertNth (0 : ℂ) y) i := by
    funext x
    apply congrArg F
    apply funext
    rw [i.forall_iff_succAbove]
    constructor
    · simp
    · intro j
      simp [i.succAbove_ne]
  rw [heq]
  exact hslice
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
