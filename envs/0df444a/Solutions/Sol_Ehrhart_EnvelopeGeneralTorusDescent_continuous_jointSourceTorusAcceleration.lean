-- Prove2me | solution 1 for Ehrhart.EnvelopeGeneralTorusDescent.continuous_jointSourceTorusAcceleration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/ef6a48f5-8e0a-4774-aa3e-c5e8e7aae0d4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_EnvelopeGeneralTorusDescent_continuous_jointSourceCoverAcceleration
import Theorems.Thm_Ehrhart_EnvelopeGeneralTorusDescent_jointSourceCoverAcceleration_spatial_periodic

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
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ m : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift m, (0 : ℂ)))
    (t : ℝ) :
    Continuous (jointSourceTorusAcceleration F t) := by
  unfold jointSourceTorusAcceleration
  exact continuous_jointSourceTorusWeight
    (continuous_jointSourceCoverAcceleration hF)
    (jointSourceCoverAcceleration_spatial_periodic hperiod) t
end Ehrhart.EnvelopeGeneralTorusDescent
