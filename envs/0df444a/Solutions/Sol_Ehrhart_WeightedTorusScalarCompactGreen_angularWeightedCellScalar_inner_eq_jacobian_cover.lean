-- Prove2me | solution 1 for Ehrhart.WeightedTorusScalarCompactGreen.angularWeightedCellScalar_inner_eq_jacobian_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/881fcb3a-28b9-476e-883a-6b80876cdf50

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_realFundamentalCell_integral_eq_coverJacobian
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_coverTest_zero_outside_fundamentalCell
import Theorems.Thm_Ehrhart_WeightedTorusScalarCompactGreen_angularWeightedCellScalar_inner_eq_unweighted

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
theorem _root_.solution {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (j : Fin n) (f : angularWeightedScalarL2 a) :
    @inner ℂ (angularWeightedCellScalarL2 a b) _
      (angularWeightedCellAdjointScalarL2 ha b hψ hψcompact j)
      (angularScalarFundamentalLiftLI ha b f) =
      logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n,
          complexTorusCoverLift (fun q : LogTorus n => f q) z *
            coverBarPartialTest ψ j z
          ∂(volume : Measure (LogSpace n))) := by
  calc
    _ = ∫ p : Space n × Space n,
          f (realTorusCoverProjection n p) *
            coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p)
          ∂(realFundamentalCellMeasure b) :=
      angularWeightedCellScalar_inner_eq_unweighted
        ha b hψ hψcompact j f
    _ = ∫ p : Space n × Space n,
          complexTorusCoverLift (fun q : LogTorus n => f q)
            (logarithmicCoordinatesEquiv n p) *
            coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p)
          ∂(realFundamentalCellMeasure b) := by
      apply integral_congr_ae
      filter_upwards [] with p
      unfold complexTorusCoverLift complexTorusCoverProjection
      rw [ContinuousLinearEquiv.symm_apply_apply]
    _ = _ := by
      apply realFundamentalCell_integral_eq_coverJacobian b
        (fun z =>
          complexTorusCoverLift (fun q : LogTorus n => f q) z *
            coverBarPartialTest ψ j z)
      intro p hp
      rw [(coverTest_zero_outside_fundamentalCell hcell p hp).2 j,
        mul_zero]
end Ehrhart.WeightedTorusScalarCompactGreen
