-- Prove2me | solution 1 for Ehrhart.RadialAccelerationBounds.sourceJointTrueRadialTimeKernelMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/752a9068-502e-400f-bb89-cb5c10ea815f

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
    0 ≤ sourceJointTrueRadialTimeKernelMass n k := by
  exact integral_nonneg (fun y => abs_nonneg _)
end Ehrhart.RadialAccelerationBounds
