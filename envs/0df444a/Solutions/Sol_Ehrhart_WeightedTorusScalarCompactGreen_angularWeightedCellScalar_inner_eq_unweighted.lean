-- Prove2me | solution 1 for Ehrhart.WeightedTorusScalarCompactGreen.angularWeightedCellScalar_inner_eq_unweighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/7a5237d4-b4a2-4f43-b54a-4fd76f7e7625

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusCompactGreen_angularScalarFundamentalLiftLI_ae_eq
import Theorems.Thm_Ehrhart_MatrixTorusCompactGreen_angularWeight_mul_inverseAngularCoverWeight
import Theorems.Thm_Ehrhart_WeightedTorusScalarCompactGreen_angularWeightedCellAdjointScalarL2_ae_eq

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
    (hψcompact : HasCompactSupport ψ) (j : Fin n)
    (f : angularWeightedScalarL2 a) :
    @inner ℂ (angularWeightedCellScalarL2 a b) _
      (angularWeightedCellAdjointScalarL2 ha b hψ hψcompact j)
      (angularScalarFundamentalLiftLI ha b f) =
        ∫ p : Space n × Space n,
          f (realTorusCoverProjection n p) *
            coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p)
          ∂(realFundamentalCellMeasure b) := by
  calc
    _ = ∫ p : Space n × Space n,
        @inner ℂ ℂ _
          (angularWeightedCellAdjointScalarTest a ψ j p)
          (f (realTorusCoverProjection n p))
        ∂(realAngularWeightedFundamentalCellMeasure a b) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards
        [angularWeightedCellAdjointScalarL2_ae_eq
          ha b hψ hψcompact j,
         angularScalarFundamentalLiftLI_ae_eq ha b f]
        with p ht hf
      rw [ht, hf]
    _ = _ := by
      have hd : Measurable
          (fun p : Space n × Space n =>
            ENNReal.ofReal
              (angularWeightedTorusDensity a
                (realTorusCoverProjection n p))) :=
        ENNReal.measurable_ofReal.comp
          ((continuous_angularWeightedTorusDensity ha).comp
            (continuous_realTorusCoverProjection n)).measurable
      rw [realAngularWeightedFundamentalCellMeasure,
        integral_withDensity_eq_integral_toReal_smul
          hd (Filter.Eventually.of_forall
            (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards [] with p
      have hc := angularWeight_mul_inverseAngularCoverWeight a p
      rw [RCLike.inner_apply]
      change
        (ENNReal.ofReal
          (angularWeightedTorusDensity a
            (realTorusCoverProjection n p))).toReal •
          (f (realTorusCoverProjection n p) *
            star (angularWeightedCellAdjointScalarTest a ψ j p)) =
          f (realTorusCoverProjection n p) *
            coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p)
      simp only [angularWeightedCellAdjointScalarTest,
        coverAdjointScalarTest, StarMul.star_mul,
        inverseAngularCoverWeight, Complex.star_def,
        Complex.conj_ofReal, starRingEnd_self_apply,
        Complex.real_smul] at hc ⊢
      calc
        _ = (((ENNReal.ofReal
              (angularWeightedTorusDensity a
                (realTorusCoverProjection n p))).toReal : ℂ) *
              (Real.exp
                (a (realTorusCoverProjection n p)) : ℂ)) *
            (coverBarPartialTest ψ j
              (logarithmicCoordinatesEquiv n p) *
              f (realTorusCoverProjection n p)) := by
            ring
        _ = _ := by rw [hc, one_mul]; ring
end Ehrhart.WeightedTorusScalarCompactGreen
