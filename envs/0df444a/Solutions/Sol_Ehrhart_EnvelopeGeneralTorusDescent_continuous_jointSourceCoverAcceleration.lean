-- Prove2me | solution 1 for Ehrhart.EnvelopeGeneralTorusDescent.continuous_jointSourceCoverAcceleration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/5971d39b-6a8f-4006-9118-a64accd524f7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.EnvelopeGeneralTorusDescent
open Set Function Filter MeasureTheory
open ComplexKillingSaturationBridge MatrixTorusBochnerIdentity JetEnvelopeGlobalPlurisubharmonic
open JetEnvelopeRightDerivative EnvelopeSmoothing EnvelopeTorusDescent
open scoped Topology ContDiff
namespace Ehrhart.EnvelopeGeneralTorusDescent
theorem _root_.solution {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F) :
    Continuous (jointSourceCoverAcceleration F) := by
  unfold jointSourceCoverAcceleration
  exact ((contDiff_jointSourceCoverVelocity hF).continuous_fderiv
    (by norm_num)).clm_apply continuous_const
end Ehrhart.EnvelopeGeneralTorusDescent
