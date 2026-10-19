-- Prove2me | solution 1 for Ehrhart.MatrixTorusCompactGreen.angularWeightedCellVector_inner_eq_unweighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/7284f25f-f24a-4605-9139-d111a5b2195e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusCompactGreen_angularFormFundamentalLiftLI_ae_eq
import Theorems.Thm_Ehrhart_MatrixTorusCompactGreen_angularWeightedCellAdjointVectorL2_ae_eq
import Theorems.Thm_Ehrhart_MatrixTorusCompactGreen_angularWeight_mul_inverseAngularCoverWeight

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusCompactGreen
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerBridge
open WeightedTorusDolbeault TorusWeightedBaseAE
open scoped BigOperators ENNReal InnerProductSpace Topology
  MatrixOrder ComplexOrder ComplexConjugate ContDiff
namespace Ehrhart.MatrixTorusCompactGreen
theorem _root_.solution {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n)
    (f : angularWeightedFormL2 a) :
    @inner ℂ (angularWeightedCellFormL2 a b) _
      (angularWeightedCellAdjointVectorL2 ha b hψ hψcompact j)
      (angularFormFundamentalLiftLI ha b f) =
        ∫ p : Space n × Space n,
          (2 : ℂ) *
            (((f (realTorusCoverProjection n p) :
              EuclideanSpace ℂ (Fin n)) j) *
                (ψ (logarithmicCoordinatesEquiv n p) : ℂ))
          ∂(realFundamentalCellMeasure b) := by
  calc
    _ = ∫ p : Space n × Space n,
        @inner ℂ (EuclideanSpace ℂ (Fin n)) _
          (angularWeightedCellAdjointVectorTest a ψ j p)
          (f (realTorusCoverProjection n p))
        ∂(realAngularWeightedFundamentalCellMeasure a b) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards
        [angularWeightedCellAdjointVectorL2_ae_eq
          ha b hψ hψcompact j,
         angularFormFundamentalLiftLI_ae_eq ha b f]
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
      unfold angularWeightedCellAdjointVectorTest coverAdjointVectorTest
      rw [inner_smul_left, EuclideanSpace.inner_single_left]
      simp only [inverseAngularCoverWeight,
        map_mul, map_ofNat, Complex.conj_ofReal,
        Complex.real_smul] at hc ⊢
      calc
        _ = (((ENNReal.ofReal
              (angularWeightedTorusDensity a
                (realTorusCoverProjection n p))).toReal : ℂ) *
              (Real.exp
                (a (realTorusCoverProjection n p)) : ℂ)) *
            ((2 : ℂ) *
              (((f (realTorusCoverProjection n p) :
                EuclideanSpace ℂ (Fin n)) j) *
                  (ψ (logarithmicCoordinatesEquiv n p) : ℂ))) := by
            ring
        _ = _ := by rw [hc, one_mul]
end Ehrhart.MatrixTorusCompactGreen
