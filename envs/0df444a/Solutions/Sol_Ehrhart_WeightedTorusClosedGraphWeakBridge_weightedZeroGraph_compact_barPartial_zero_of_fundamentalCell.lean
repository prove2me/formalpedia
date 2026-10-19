-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedZeroGraph_compact_barPartial_zero_of_fundamentalCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/08177f33-0eee-45f0-ade8-a2071c5361e2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedCellWeakAdjointFunctional_apply
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedCellScalar_inner_eq_jacobian_cover
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedCellWeakAdjointFunctional_closedGraph_zero

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
theorem _root_.solution
    {n k : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    (f : weightedTorusScalarL2 k φ)
    (hf : WithLp.toLp 2 (f, (0 : weightedTorusFormL2 k φ)) ∈
      functionDolbeaultGraph k φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      complexTorusCoverLift
        (fun p : WeightedTorusHilbert.LogTorus n => f p) z *
          coverBarPartialTest ψ j z
      ∂(volume : Measure (TorusCharacters.LogSpace n))) = 0 := by
  have hz := weightedCellWeakAdjointFunctional_closedGraph_zero
    hφ b hψ hψcompact hcell j
    (WithLp.toLp 2 (f, (0 : weightedTorusFormL2 k φ))) hf
  rw [weightedCellWeakAdjointFunctional_apply] at hz
  change
    @inner ℂ (weightedCellScalarL2 k φ b) _
      (weightedCellAdjointScalarL2 (k := k) hφ b hψ hψcompact j)
      (weightedScalarFundamentalLiftLI k φ b f) +
    @inner ℂ (weightedCellFormL2 k φ b) _
      (weightedCellAdjointVectorL2 (k := k) hφ b hψ hψcompact j)
      (weightedFormFundamentalLiftLI k φ b
        (0 : weightedTorusFormL2 k φ)) = 0 at hz
  rw [map_zero, inner_zero_right, add_zero,
    weightedCellScalar_inner_eq_jacobian_cover
      hφ b hψ hψcompact hcell j] at hz
  exact (smul_eq_zero.mp hz).resolve_left
    (logarithmicCoverJacobianFactor_pos n).ne'
end Ehrhart.WeightedTorusClosedGraphWeakBridge
