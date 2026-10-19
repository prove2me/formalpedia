-- Prove2me | solution 1 for Ehrhart.RadialAccelerationBounds.hasCompactSupport_sourceJointTrueRadialTimeKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/e908b837-8ebf-4e74-83a7-6f8647497e49

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
    HasCompactSupport (sourceJointTrueRadialTimeKernel n k) := by
  exact (hasCompactSupport_sourceJointTrueRadialMollifier n k).fderiv_apply
    ℝ (sourceJointTimeDirection n)
end Ehrhart.RadialAccelerationBounds
