-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellVector_inner_eq_unweighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/06d3a952-b557-45f0-8b18-4593b7d05c11

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_radialWeight_lt_top
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedFormFundamentalLiftLI_ae_eq
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedCellAdjointVectorL2_ae_eq
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_radialWeight_mul_inverseRealCoverWeight

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
    (f : weightedTorusFormL2 k φ) :
    @inner ℂ (weightedCellFormL2 k φ b) _
      (weightedCellAdjointVectorL2 (k := k) hφ b hψ hψcompact j)
      (weightedFormFundamentalLiftLI k φ b f) =
        ∫ p : Space n × Space n,
          (2 : ℂ) *
            (((f (realTorusCoverProjection n p) :
              EuclideanSpace ℂ (Fin n)) j) *
                (ψ (logarithmicCoordinatesEquiv n p) : ℂ))
          ∂(realFundamentalCellMeasure b) := by
  calc
    _ = ∫ p : Space n × Space n,
        @inner ℂ (EuclideanSpace ℂ (Fin n)) _
          (weightedCellAdjointVectorTest k φ ψ j p)
          (f (realTorusCoverProjection n p))
        ∂(realWeightedFundamentalCellMeasure k φ b) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards
        [weightedCellAdjointVectorL2_ae_eq (k := k)
          hφ b hψ hψcompact j,
         weightedFormFundamentalLiftLI_ae_eq φ b f] with p ha hf
      rw [ha, hf]
    _ = _ := by
      have hd : Measurable
          (fun p : Space n × Space n =>
            radialWeight k φ p.1) :=
        (radialWeight_measurable k hφ).comp measurable_fst
      rw [realWeightedFundamentalCellMeasure_eq_withDensity hφ b,
        integral_withDensity_eq_integral_toReal_smul
          hd
          (Filter.Eventually.of_forall
            (fun p : Space n × Space n =>
              radialWeight_lt_top φ p.1))]
      apply integral_congr_ae
      filter_upwards [] with p
      have hc := radialWeight_mul_inverseRealCoverWeight (k := k) φ p
      unfold weightedCellAdjointVectorTest coverAdjointVectorTest
      rw [inner_smul_left, EuclideanSpace.inner_single_left]
      simp only [inverseRealCoverWeight,
        map_mul, map_ofNat, Complex.conj_ofReal,
        Complex.real_smul] at hc ⊢
      calc
        _ =
          (((radialWeight k φ p.1).toReal : ℂ) *
            (Real.exp ((k : ℝ) * φ p.1) : ℂ)) *
            ((2 : ℂ) *
              (((f (realTorusCoverProjection n p) :
                EuclideanSpace ℂ (Fin n)) j) *
                (ψ (logarithmicCoordinatesEquiv n p) : ℂ))) := by ring
        _ = _ := by rw [hc, one_mul]
end Ehrhart.WeightedTorusClosedGraphWeakBridge
