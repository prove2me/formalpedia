-- Prove2me | solution 1 for Ehrhart.MatrixTorusCompactGreen.angularWeightedCellVector_inner_eq_jacobian_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/3cdd0bae-891f-4f1f-9671-2ab5cfb9440d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_realFundamentalCell_integral_eq_coverJacobian
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_coverTest_zero_outside_fundamentalCell
import Theorems.Thm_Ehrhart_MatrixTorusCompactGreen_angularWeightedCellVector_inner_eq_unweighted

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
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (j : Fin n) (f : angularWeightedFormL2 a) :
    @inner ℂ (angularWeightedCellFormL2 a b) _
      (angularWeightedCellAdjointVectorL2 ha b hψ hψcompact j)
      (angularFormFundamentalLiftLI ha b f) =
      logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n,
          (2 : ℂ) *
            (complexTorusCoverLift
              (fun q : LogTorus n =>
                (f q : EuclideanSpace ℂ (Fin n)) j) z *
                (ψ z : ℂ))
          ∂(volume : Measure (LogSpace n))) := by
  calc
    _ = ∫ p : Space n × Space n,
        (2 : ℂ) *
          (((f (realTorusCoverProjection n p) :
            EuclideanSpace ℂ (Fin n)) j) *
              (ψ (logarithmicCoordinatesEquiv n p) : ℂ))
        ∂(realFundamentalCellMeasure b) :=
      angularWeightedCellVector_inner_eq_unweighted
        ha b hψ hψcompact j f
    _ = ∫ p : Space n × Space n,
        (2 : ℂ) *
          (complexTorusCoverLift
            (fun q : LogTorus n =>
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
              (fun q : LogTorus n =>
                (f q : EuclideanSpace ℂ (Fin n)) j) z *
                  (ψ z : ℂ)))
      intro p hp
      rw [(coverTest_zero_outside_fundamentalCell hcell p hp).1]
      simp
end Ehrhart.MatrixTorusCompactGreen
