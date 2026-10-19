-- Prove2me | solution 1 for Ehrhart.RadialAccelerationBounds.jointSourceCoverVelocity_sourceJointTrueRadialSmoothed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/17f25f72-25fa-4679-80ba-08b9617640de

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.RadialAccelerationBounds
open Set Filter Function MeasureTheory
open JetEnvelopeGlobalPlurisubharmonic EnvelopeTorusDescent EnvelopeGeneralTorusDescent
open JetEnvelopeTrueRadialMollifier
open scoped Topology ENNReal Convolution ContDiff
attribute [local instance] Ehrhart.RadialAccelerationBounds.sourceJointCoverVolume_isAddHaar
namespace Ehrhart.RadialAccelerationBounds
theorem _root_.solution
    {n : ℕ} {f : SourceJointComplexCover n → ℝ}
    (hf : LocallyIntegrable f
      (volume : Measure (SourceJointComplexCover n)))
    (k : ℕ) (q : SourceJointComplexCover n) :
    jointSourceCoverVelocity (sourceJointTrueRadialSmoothed f k) q =
      (sourceJointTrueRadialTimeKernel n k
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (SourceJointComplexCover n))] f) q := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  let κ : SourceJointComplexCover n → ℝ :=
    sourceJointTrueRadialMollifier n k
  let v : SourceJointComplexCover n := sourceJointTimeDirection n
  have hκ : ContDiff ℝ 1 κ :=
    (contDiff_sourceJointTrueRadialMollifier n k).of_le (by simp)
  have hc : HasCompactSupport κ :=
    hasCompactSupport_sourceJointTrueRadialMollifier n k
  have hd := hc.hasFDerivAt_convolution_left L hκ hf q
  have hint : Integrable
      (fun y : SourceJointComplexCover n =>
        (L.precompL (SourceJointComplexCover n))
          (fderiv ℝ κ y) (f (q - y)))
      (volume : Measure (SourceJointComplexCover n)) :=
    (hc.fderiv ℝ).convolutionExists_left
      (L.precompL (SourceJointComplexCover n))
      (hκ.continuous_fderiv (by simp)) hf q
  change
    (fderiv ℝ
      (κ ⋆[L, (volume : Measure (SourceJointComplexCover n))] f)
      q) v =
    (sourceJointTrueRadialTimeKernel n k
      ⋆[L, (volume : Measure (SourceJointComplexCover n))] f) q
  rw [hd.fderiv, MeasureTheory.convolution_def,
    ContinuousLinearMap.integral_apply hint,
    MeasureTheory.convolution_def]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [sourceJointTrueRadialTimeKernel, L, κ, v,
    ContinuousLinearMap.precompL_apply]
end Ehrhart.RadialAccelerationBounds
