-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellAdjointScalarL2_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/e5000bf3-39a8-4836-b291-33af6e6ff127

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
theorem _root_.solution {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    (fun p : Space n × Space n =>
      weightedCellAdjointScalarL2 (k := k) hφ b hψ hψcompact j p) =ᵐ[
        realWeightedFundamentalCellMeasure k φ b]
      weightedCellAdjointScalarTest k φ ψ j := by
  let : IsLocallyFiniteMeasure
      (realWeightedFundamentalCellMeasure k φ b) :=
    realWeightedFundamentalCellMeasure_isLocallyFinite hφ b
  simpa only [weightedCellAdjointScalarL2] using
    (MeasureTheory.MemLp.coeFn_toLp
      ((continuous_weightedCellAdjointScalarTest hφ hψ j).memLp_of_hasCompactSupport
          (μ := realWeightedFundamentalCellMeasure k φ b)
          (compactSupport_weightedCellAdjointScalarTest φ hψcompact j)))
end Ehrhart.WeightedTorusClosedGraphWeakBridge
