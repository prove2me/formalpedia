-- Prove2me | solution 1 for Ehrhart.RadialAccelerationBounds.integrable_sourceJointTrueRadialTimeKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/37cbbf60-f6b4-471b-ae2b-6552ec4e4589

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_RadialAccelerationBounds_hasCompactSupport_sourceJointTrueRadialTimeKernel
import Theorems.Thm_Ehrhart_RadialAccelerationBounds_continuous_sourceJointTrueRadialTimeKernel

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
    Integrable (sourceJointTrueRadialTimeKernel n k)
      (volume : Measure (SourceJointComplexCover n)) :=
  (continuous_sourceJointTrueRadialTimeKernel n k).integrable_of_hasCompactSupport
    (hasCompactSupport_sourceJointTrueRadialTimeKernel n k)
end Ehrhart.RadialAccelerationBounds
