-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.coverBarPartialTest_eq_zero_of_notMem_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/535a6c10-8290-468d-b7d2-5e0d28eaf4d6

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusClosedGraphWeakBridge
open Set Function MeasureTheory Filter
open WeightedTorusHilbert WeightedBrascampSaturation ComplexKillingSaturationBridge
open DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
  Manifold ContDiff
namespace Ehrhart.WeightedTorusClosedGraphWeakBridge
theorem _root_.solution {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (j : Fin n) {z : TorusCharacters.LogSpace n}
    (hz : z ∉ tsupport ψ) :
    coverBarPartialTest ψ j z = 0 := by
  unfold coverBarPartialTest
  rw [fderiv_of_notMem_tsupport ℝ hz]
  simp
end Ehrhart.WeightedTorusClosedGraphWeakBridge
