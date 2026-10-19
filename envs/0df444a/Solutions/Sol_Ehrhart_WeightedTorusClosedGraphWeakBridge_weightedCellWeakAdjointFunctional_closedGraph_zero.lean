-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellWeakAdjointFunctional_closedGraph_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/faef9998-ad91-4038-88c0-b6d94ce2abb6

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedCellWeakAdjointFunctional_smoothGraph_zero

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
    (j : Fin n) (v : functionDolbeaultGraphAmbient k φ)
    (hv : v ∈ functionDolbeaultGraph k φ) :
    weightedCellWeakAdjointFunctional
      hφ b hψ hψcompact j v = 0 := by
  let L : functionDolbeaultGraphAmbient k φ →L[ℂ] ℂ :=
    weightedCellWeakAdjointFunctional hφ b hψ hψcompact j
  have hspan :
      Submodule.span ℂ (smoothFunctionDolbeaultGraphSet k φ) ≤
        L.ker := by
    apply Submodule.span_le.mpr
    intro v hv'
    rcases hv' with ⟨F, hF, hperiod, _hcompact, hFLp, hDLp, rfl⟩
    change
      L (WithLp.toLp 2
        (torusScalarL2OfRepresentative φ F hFLp,
         torusFunctionBarPartialL2 φ F hDLp)) = 0
    exact weightedCellWeakAdjointFunctional_smoothGraph_zero
      hφ b hψ hψcompact hcell
      (hF.of_le (by norm_num)) hperiod hFLp hDLp j
  have hgraph : functionDolbeaultGraph k φ ≤ L.ker := by
    unfold functionDolbeaultGraph
    exact Submodule.topologicalClosure_minimal
      (Submodule.span ℂ (smoothFunctionDolbeaultGraphSet k φ))
      hspan L.isClosed_ker
  exact hgraph hv
end Ehrhart.WeightedTorusClosedGraphWeakBridge
