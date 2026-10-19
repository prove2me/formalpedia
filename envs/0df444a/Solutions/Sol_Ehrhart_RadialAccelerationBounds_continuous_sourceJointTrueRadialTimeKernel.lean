-- Prove2me | solution 1 for Ehrhart.RadialAccelerationBounds.continuous_sourceJointTrueRadialTimeKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/7d4210ff-5e98-4e38-8428-8e28d74e4464

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
theorem _root_.solution (n k : ℕ) :
    Continuous (sourceJointTrueRadialTimeKernel n k) := by
  unfold sourceJointTrueRadialTimeKernel
  exact ((contDiff_sourceJointTrueRadialMollifier n k).continuous_fderiv
    (by simp)).clm_apply continuous_const
end Ehrhart.RadialAccelerationBounds
