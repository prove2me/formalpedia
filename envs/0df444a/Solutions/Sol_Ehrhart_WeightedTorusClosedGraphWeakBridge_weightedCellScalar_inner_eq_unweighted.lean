-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellScalar_inner_eq_unweighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/6bf9ce3f-0293-413c-be19-1dd125af28f1

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_radialWeight_lt_top
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedScalarFundamentalLiftLI_ae_eq
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedCellAdjointScalarL2_ae_eq
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
    (f : weightedTorusScalarL2 k φ) :
    @inner ℂ (weightedCellScalarL2 k φ b) _
      (weightedCellAdjointScalarL2 (k := k) hφ b hψ hψcompact j)
      (weightedScalarFundamentalLiftLI k φ b f) =
        ∫ p : Space n × Space n,
          f (realTorusCoverProjection n p) *
            coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p)
          ∂(realFundamentalCellMeasure b) := by
  calc
    _ = ∫ p : Space n × Space n,
        @inner ℂ ℂ _
          (weightedCellAdjointScalarTest k φ ψ j p)
          (f (realTorusCoverProjection n p))
        ∂(realWeightedFundamentalCellMeasure k φ b) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards
        [weightedCellAdjointScalarL2_ae_eq (k := k)
          hφ b hψ hψcompact j,
         weightedScalarFundamentalLiftLI_ae_eq φ b f] with p ha hf
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
      rw [RCLike.inner_apply]
      change
        (radialWeight k φ p.1).toReal •
          (f (realTorusCoverProjection n p) *
            star (weightedCellAdjointScalarTest k φ ψ j p)) =
          f (realTorusCoverProjection n p) *
            coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p)
      simp only [weightedCellAdjointScalarTest,
        coverAdjointScalarTest, star_mul,
        inverseRealCoverWeight, Complex.star_def, Complex.conj_ofReal,
        starRingEnd_self_apply,
        Complex.real_smul] at hc ⊢
      calc
        _ =
          (((radialWeight k φ p.1).toReal : ℂ) *
            (Real.exp ((k : ℝ) * φ p.1) : ℂ)) *
            (coverBarPartialTest ψ j
              (logarithmicCoordinatesEquiv n p) *
              f (realTorusCoverProjection n p)) := by ring
        _ = _ := by rw [hc, one_mul]; ring
end Ehrhart.WeightedTorusClosedGraphWeakBridge
