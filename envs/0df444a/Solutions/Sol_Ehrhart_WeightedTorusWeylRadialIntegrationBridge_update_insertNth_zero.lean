-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.update_insertNth_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/87e8cd8d-0186-4dba-a580-0a4fca313f85

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
    (i : Fin (n + 1)) (x : ℂ)
    (y : TorusCharacters.LogSpace n) :
    Function.update
      (i.insertNth x y : Fin (n + 1) → ℂ) i 0 =
      (i.insertNth (0 : ℂ) y : Fin (n + 1) → ℂ) := by
  apply funext
  rw [i.forall_iff_succAbove]
  constructor
  · simp
  · intro j
    simp [i.succAbove_ne]
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
