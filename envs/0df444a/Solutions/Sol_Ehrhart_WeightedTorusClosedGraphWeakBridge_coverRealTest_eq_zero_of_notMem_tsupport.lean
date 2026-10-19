-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.coverRealTest_eq_zero_of_notMem_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/2f5352f1-8928-4d3d-b8a3-ef3d23e9bb69

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
    {z : TorusCharacters.LogSpace n}
    (hz : z ∉ tsupport ψ) :
    ψ z = 0 := by
  by_contra hn
  apply hz
  exact subset_closure hn
end Ehrhart.WeightedTorusClosedGraphWeakBridge
