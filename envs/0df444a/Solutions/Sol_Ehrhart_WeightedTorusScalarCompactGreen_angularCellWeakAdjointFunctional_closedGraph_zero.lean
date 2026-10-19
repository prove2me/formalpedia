-- Prove2me | solution 1 for Ehrhart.WeightedTorusScalarCompactGreen.angularCellWeakAdjointFunctional_closedGraph_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/d729b5c9-86ac-445b-b1d3-4912dfbc26d4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusScalarCompactGreen_angularCellWeakAdjointFunctional_smoothGraph_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusScalarCompactGreen
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault
open TorusWeakDolbeaultMollification TorusMollifiedBochner BergmanJetStrictMixedLocalCore
open MatrixTorusCompactGreen
open scoped BigOperators ENNReal InnerProductSpace Topology
  ComplexConjugate ContDiff Convolution Manifold
namespace Ehrhart.WeightedTorusScalarCompactGreen
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (j : Fin n) (v : angularDolbeaultGraphAmbient a)
    (hv : v ∈ angularDolbeaultGraph a) :
    angularCellWeakAdjointFunctional ha b hψ hψcompact j v = 0 := by
  let L : angularDolbeaultGraphAmbient a →L[ℂ] ℂ :=
    angularCellWeakAdjointFunctional ha b hψ hψcompact j
  have hspan :
      Submodule.span ℂ (smoothAngularDolbeaultGraphSet a) ≤ L.ker := by
    apply Submodule.span_le.mpr
    intro v hv'
    rcases hv' with
      ⟨F, hF, hperiod, _hcompact, hFLp, hDLp, rfl⟩
    exact angularCellWeakAdjointFunctional_smoothGraph_zero
      ha b hψ hψcompact hcell
      (hF.of_le (by norm_num)) hperiod hFLp hDLp j
  have hgraph : angularDolbeaultGraph a ≤ L.ker := by
    unfold angularDolbeaultGraph
    exact Submodule.topologicalClosure_minimal
      (Submodule.span ℂ (smoothAngularDolbeaultGraphSet a))
      hspan L.isClosed_ker
  exact hgraph hv
end Ehrhart.WeightedTorusScalarCompactGreen
