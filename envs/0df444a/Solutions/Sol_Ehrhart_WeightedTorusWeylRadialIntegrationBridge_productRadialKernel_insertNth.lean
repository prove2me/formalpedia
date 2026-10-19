-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.productRadialKernel_insertNth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/430bf3d3-7f38-4bb9-b690-d425faa81833

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
    (i : Fin (n + 1)) (w : ℂ)
    (y : Fin n → ℂ) :
    productRadialKernel (i.insertNth w y) =
      radialCoordinateKernel w * productRadialKernel y := by
  unfold productRadialKernel
  have hfun :
      (fun j : Fin (n + 1) =>
        radialCoordinateKernel
          ((i.insertNth w y : Fin (n + 1) → ℂ) j)) =
        (i.insertNth (radialCoordinateKernel w)
          (fun j : Fin n => radialCoordinateKernel (y j)) :
            Fin (n + 1) → ℝ) := by
    apply funext
    rw [i.forall_iff_succAbove]
    constructor
    · simp
    · intro j
      simp
  rw [hfun]
  exact Fin.prod_insertNth i (radialCoordinateKernel w)
    (fun j : Fin n => radialCoordinateKernel (y j))
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
