-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellWeakAdjointFunctional_smoothGraph_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/04b8e54d-6028-46c8-b3e8-cc524605b9f5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusGraphWeakBridge_weightedSmoothGraphGenerator_compact_barPartial_green
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedCellWeakAdjointFunctional_apply
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedCellScalar_inner_eq_jacobian_cover
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedCellVector_inner_eq_jacobian_cover

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
    (hφ : Continuous φ) (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF₁ : ContDiff ℝ 1 F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hF : MemLp (torusScalarRepresentative F) 2
      (weightedTorusMeasure k φ))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (weightedTorusMeasure k φ)) (j : Fin n) :
    weightedCellWeakAdjointFunctional (k := k)
      hφ b hψ hψcompact j
        (WithLp.toLp 2
          (torusScalarL2OfRepresentative φ F hF,
           torusFunctionBarPartialL2 φ F hD)) = 0 := by
  rw [weightedCellWeakAdjointFunctional_apply]
  change
    @inner ℂ (weightedCellScalarL2 k φ b) _
      (weightedCellAdjointScalarL2 (k := k) hφ b hψ hψcompact j)
      (weightedScalarFundamentalLiftLI k φ b
        (torusScalarL2OfRepresentative φ F hF)) +
    @inner ℂ (weightedCellFormL2 k φ b) _
      (weightedCellAdjointVectorL2 (k := k) hφ b hψ hψcompact j)
      (weightedFormFundamentalLiftLI k φ b
        (torusFunctionBarPartialL2 φ F hD)) = 0
  rw [weightedCellScalar_inner_eq_jacobian_cover
    hφ b hψ hψcompact hcell j,
    weightedCellVector_inner_eq_jacobian_cover
      hφ b hψ hψcompact hcell j,
    ← smul_add, integral_const_mul,
    weightedSmoothGraphGenerator_compact_barPartial_green
      hφ F hF₁ hperiod hF hD hψ hψcompact j]
  simp
end Ehrhart.WeightedTorusClosedGraphWeakBridge
