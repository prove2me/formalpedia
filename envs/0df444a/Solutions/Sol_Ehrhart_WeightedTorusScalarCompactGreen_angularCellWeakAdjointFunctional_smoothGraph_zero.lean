-- Prove2me | solution 1 for Ehrhart.WeightedTorusScalarCompactGreen.angularCellWeakAdjointFunctional_smoothGraph_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/b1b74d08-a7f6-47bf-b2c0-36c36a4cf928

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultGraphDistributionBridge_complex_compact_barPartial_green
import Theorems.Thm_Ehrhart_MatrixTorusCompactGreen_angularWeightedCellVector_inner_eq_jacobian_cover
import Theorems.Thm_Ehrhart_MatrixTorusCompactGreen_angularFormGraphGenerator_complexCoverLift_ae_eq
import Theorems.Thm_Ehrhart_WeightedTorusScalarCompactGreen_angularWeightedCellScalar_inner_eq_jacobian_cover
import Theorems.Thm_Ehrhart_WeightedTorusScalarCompactGreen_angularCellWeakAdjointFunctional_apply
import Theorems.Thm_Ehrhart_WeightedTorusScalarCompactGreen_angularScalarGraphGenerator_complexCoverLift_ae_eq

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
    {F : LogSpace n → ℂ} (hF₁ : ContDiff ℝ 1 F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (imaginaryShift q))
    (hF : MemLp (torusScalarRepresentative F) 2
      (angularWeightedTorusMeasure a))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (angularWeightedTorusMeasure a)) (j : Fin n) :
    angularCellWeakAdjointFunctional ha b hψ hψcompact j
      (WithLp.toLp 2
        (angularScalarL2OfRepresentative a F hF,
         angularBarPartialL2OfRepresentative a F hD)) = 0 := by
  rw [angularCellWeakAdjointFunctional_apply]
  change
    @inner ℂ (angularWeightedCellScalarL2 a b) _
      (angularWeightedCellAdjointScalarL2 ha b hψ hψcompact j)
      (angularScalarFundamentalLiftLI ha b
        (angularScalarL2OfRepresentative a F hF)) +
    @inner ℂ (angularWeightedCellFormL2 a b) _
      (angularWeightedCellAdjointVectorL2 ha b hψ hψcompact j)
      (angularFormFundamentalLiftLI ha b
        (angularBarPartialL2OfRepresentative a F hD)) = 0
  rw [angularWeightedCellScalar_inner_eq_jacobian_cover
    ha b hψ hψcompact hcell j,
    angularWeightedCellVector_inner_eq_jacobian_cover
      ha b hψ hψcompact hcell j]
  have hgreen :
      (∫ z : LogSpace n,
        complexTorusCoverLift
          (fun q : LogTorus n =>
            angularScalarL2OfRepresentative a F hF q) z *
            coverBarPartialTest ψ j z
        ∂(volume : Measure (LogSpace n))) =
        -(2 : ℂ) *
          (∫ z : LogSpace n,
            complexTorusCoverLift
              (fun q : LogTorus n =>
                (angularBarPartialL2OfRepresentative a F hD q :
                  EuclideanSpace ℂ (Fin n)) j) z * (ψ z : ℂ)
            ∂(volume : Measure (LogSpace n))) := by
    calc
      _ = ∫ z : LogSpace n,
          F z * coverBarPartialTest ψ j z
          ∂(volume : Measure (LogSpace n)) := by
        apply integral_congr_ae
        filter_upwards
          [angularScalarGraphGenerator_complexCoverLift_ae_eq
            ha F hperiod hF] with z hz
        rw [hz]
      _ = -(2 : ℂ) *
          (∫ z : LogSpace n,
            barPartialCoordinate F z j * (ψ z : ℂ)
              ∂(volume : Measure (LogSpace n))) :=
        complex_compact_barPartial_green hF₁ hψ hψcompact j
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards
          [angularFormGraphGenerator_complexCoverLift_ae_eq
            ha F hperiod hD j] with z hz
        rw [hz]
  rw [integral_const_mul]
  rw [← smul_add, hgreen]
  simp
end Ehrhart.WeightedTorusScalarCompactGreen
