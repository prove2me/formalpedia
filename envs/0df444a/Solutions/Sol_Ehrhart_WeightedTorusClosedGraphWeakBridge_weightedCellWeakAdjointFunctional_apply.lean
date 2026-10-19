-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellWeakAdjointFunctional_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/92f99a78-9333-44c0-bf98-3c3a26d68e6e

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
    (hψcompact : HasCompactSupport ψ) (j : Fin n)
    (v : functionDolbeaultGraphAmbient k φ) :
    weightedCellWeakAdjointFunctional hφ b hψ hψcompact j v =
      @inner ℂ (weightedCellScalarL2 k φ b) _
        (weightedCellAdjointScalarL2 hφ b hψ hψcompact j)
        (weightedScalarFundamentalLiftLI k φ b (WithLp.fst v)) +
      @inner ℂ (weightedCellFormL2 k φ b) _
        (weightedCellAdjointVectorL2 hφ b hψ hψcompact j)
        (weightedFormFundamentalLiftLI k φ b (WithLp.snd v)) := by
  rfl
end Ehrhart.WeightedTorusClosedGraphWeakBridge
