-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellVector_inner_eq_jacobian_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/724d64dd-2ba9-4013-9c12-0f1ee2a9d55f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedCellVector_inner_eq_unweighted
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_realFundamentalCell_integral_eq_coverJacobian
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_coverTest_zero_outside_fundamentalCell

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
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (j : Fin n) (f : weightedTorusFormL2 k φ) :
    @inner ℂ (weightedCellFormL2 k φ b) _
      (weightedCellAdjointVectorL2 (k := k) hφ b hψ hψcompact j)
      (weightedFormFundamentalLiftLI k φ b f) =
      logarithmicCoverJacobianFactor n •
        (∫ z : TorusCharacters.LogSpace n,
          (2 : ℂ) *
            (complexTorusCoverLift
              (fun p : WeightedTorusHilbert.LogTorus n =>
                (f p : EuclideanSpace ℂ (Fin n)) j) z *
                (ψ z : ℂ))
          ∂(volume : Measure
            (TorusCharacters.LogSpace n))) := by
  calc
    _ = ∫ p : Space n × Space n,
        (2 : ℂ) *
          (((f (realTorusCoverProjection n p) :
            EuclideanSpace ℂ (Fin n)) j) *
              (ψ (logarithmicCoordinatesEquiv n p) : ℂ))
        ∂(realFundamentalCellMeasure b) :=
      weightedCellVector_inner_eq_unweighted
        hφ b hψ hψcompact j f
    _ = ∫ p : Space n × Space n,
        (2 : ℂ) *
          (complexTorusCoverLift
            (fun q : WeightedTorusHilbert.LogTorus n =>
              (f q : EuclideanSpace ℂ (Fin n)) j)
              (logarithmicCoordinatesEquiv n p) *
            (ψ (logarithmicCoordinatesEquiv n p) : ℂ))
        ∂(realFundamentalCellMeasure b) := by
      apply integral_congr_ae
      filter_upwards [] with p
      unfold complexTorusCoverLift complexTorusCoverProjection
      rw [ContinuousLinearEquiv.symm_apply_apply]
    _ = _ := by
      apply realFundamentalCell_integral_eq_coverJacobian b
        (fun z =>
          (2 : ℂ) *
            (complexTorusCoverLift
              (fun p : WeightedTorusHilbert.LogTorus n =>
                (f p : EuclideanSpace ℂ (Fin n)) j) z *
                (ψ z : ℂ)))
      intro p hp
      rw [(coverTest_zero_outside_fundamentalCell hcell p hp).1]
      simp
end Ehrhart.WeightedTorusClosedGraphWeakBridge
