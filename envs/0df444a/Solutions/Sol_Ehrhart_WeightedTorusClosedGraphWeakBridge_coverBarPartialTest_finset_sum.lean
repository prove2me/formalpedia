-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.coverBarPartialTest_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/2c84d3cc-04d7-418f-ac76-fd5d808c57f3

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
    {ι : Type*} (s : Finset ι)
    (ψ : ι → TorusCharacters.LogSpace n → ℝ)
    (hψ : ∀ i ∈ s, ContDiff ℝ 1 (ψ i))
    (j : Fin n) (z : TorusCharacters.LogSpace n) :
    coverBarPartialTest (fun w => ∑ i ∈ s, ψ i w) j z =
      ∑ i ∈ s, coverBarPartialTest (ψ i) j z := by
  unfold coverBarPartialTest
  rw [fderiv_fun_sum
    (fun i hi => (hψ i hi).differentiable (by simp) z)]
  simp [Finset.mul_sum, Finset.sum_add_distrib]
end Ehrhart.WeightedTorusClosedGraphWeakBridge
