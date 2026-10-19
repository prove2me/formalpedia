-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedCellScalar_inner_eq_jacobian_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/d174fdc7-c3f8-48e5-8695-15c70c5bfe71

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedCellScalar_inner_eq_unweighted
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
    (j : Fin n) (f : weightedTorusScalarL2 k φ) :
    @inner ℂ (weightedCellScalarL2 k φ b) _
      (weightedCellAdjointScalarL2 (k := k) hφ b hψ hψcompact j)
      (weightedScalarFundamentalLiftLI k φ b f) =
      logarithmicCoverJacobianFactor n •
        (∫ z : TorusCharacters.LogSpace n,
          complexTorusCoverLift
            (fun p : WeightedTorusHilbert.LogTorus n => f p) z *
              coverBarPartialTest ψ j z
          ∂(volume : Measure
            (TorusCharacters.LogSpace n))) := by
  calc
    _ = ∫ p : Space n × Space n,
        f (realTorusCoverProjection n p) *
          coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p)
        ∂(realFundamentalCellMeasure b) :=
      weightedCellScalar_inner_eq_unweighted
        hφ b hψ hψcompact j f
    _ = ∫ p : Space n × Space n,
        (complexTorusCoverLift
          (fun q : WeightedTorusHilbert.LogTorus n => f q)
          (logarithmicCoordinatesEquiv n p)) *
          coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p)
        ∂(realFundamentalCellMeasure b) := by
      apply integral_congr_ae
      filter_upwards [] with p
      unfold complexTorusCoverLift complexTorusCoverProjection
      rw [ContinuousLinearEquiv.symm_apply_apply]
    _ = _ := by
      apply realFundamentalCell_integral_eq_coverJacobian b
        (fun z =>
          complexTorusCoverLift
            (fun p : WeightedTorusHilbert.LogTorus n => f p) z *
              coverBarPartialTest ψ j z)
      intro p hp
      rw [(coverTest_zero_outside_fundamentalCell hcell p hp).2 j,
        mul_zero]
end Ehrhart.WeightedTorusClosedGraphWeakBridge
