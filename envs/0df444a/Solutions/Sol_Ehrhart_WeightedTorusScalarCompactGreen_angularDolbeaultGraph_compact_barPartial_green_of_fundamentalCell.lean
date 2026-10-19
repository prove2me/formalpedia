-- Prove2me | solution 1 for Ehrhart.WeightedTorusScalarCompactGreen.angularDolbeaultGraph_compact_barPartial_green_of_fundamentalCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/5a43bbef-f699-4426-97f4-74a819fab2d2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusCompactGreen_angularWeightedCellVector_inner_eq_jacobian_cover
import Theorems.Thm_Ehrhart_WeightedTorusScalarCompactGreen_angularWeightedCellScalar_inner_eq_jacobian_cover
import Theorems.Thm_Ehrhart_WeightedTorusScalarCompactGreen_angularCellWeakAdjointFunctional_apply
import Theorems.Thm_Ehrhart_WeightedTorusScalarCompactGreen_angularCellWeakAdjointFunctional_closedGraph_zero

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
    (f : angularWeightedScalarL2 a)
    (W : angularWeightedFormL2 a)
    (hgraph : WithLp.toLp 2 (f, W) ∈ angularDolbeaultGraph a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (j : Fin n) :
    (∫ z : LogSpace n,
      complexTorusCoverLift (fun q : LogTorus n => f q) z *
        coverBarPartialTest ψ j z
      ∂(volume : Measure (LogSpace n))) =
      -(2 : ℂ) *
        (∫ z : LogSpace n,
          complexTorusCoverLift
            (fun q : LogTorus n =>
              (W q : EuclideanSpace ℂ (Fin n)) j) z * (ψ z : ℂ)
          ∂(volume : Measure (LogSpace n))) := by
  have hz := angularCellWeakAdjointFunctional_closedGraph_zero
    ha b hψ hψcompact hcell j (WithLp.toLp 2 (f, W)) hgraph
  rw [angularCellWeakAdjointFunctional_apply] at hz
  change
    @inner ℂ (angularWeightedCellScalarL2 a b) _
      (angularWeightedCellAdjointScalarL2 ha b hψ hψcompact j)
      (angularScalarFundamentalLiftLI ha b f) +
    @inner ℂ (angularWeightedCellFormL2 a b) _
      (angularWeightedCellAdjointVectorL2 ha b hψ hψcompact j)
      (angularFormFundamentalLiftLI ha b W) = 0 at hz
  rw [angularWeightedCellScalar_inner_eq_jacobian_cover
    ha b hψ hψcompact hcell j,
    angularWeightedCellVector_inner_eq_jacobian_cover
      ha b hψ hψcompact hcell j, ← smul_add] at hz
  have hinner :
      (∫ z : LogSpace n,
        complexTorusCoverLift (fun q : LogTorus n => f q) z *
          coverBarPartialTest ψ j z
        ∂(volume : Measure (LogSpace n))) +
      (∫ z : LogSpace n,
        (2 : ℂ) *
          (complexTorusCoverLift
            (fun q : LogTorus n =>
              (W q : EuclideanSpace ℂ (Fin n)) j) z * (ψ z : ℂ))
        ∂(volume : Measure (LogSpace n))) = 0 :=
    (smul_eq_zero.mp hz).resolve_left
      (logarithmicCoverJacobianFactor_pos n).ne'
  rw [integral_const_mul] at hinner
  linear_combination hinner
end Ehrhart.WeightedTorusScalarCompactGreen
