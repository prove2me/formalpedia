-- Prove2me | solution 1 for Ehrhart.EnvelopeGeneralTorusDescent.jointSourceCoverAcceleration_spatial_periodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/f4d08d6d-3e34-4acf-b52b-596677076648

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
    (hperiod : ∀ m : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift m, (0 : ℂ)))
    (m : Fin n → ℤ) :
    Function.Periodic (jointSourceCoverAcceleration F)
      (TorusCharacters.imaginaryShift m, (0 : ℂ)) := by
  intro q
  unfold jointSourceCoverAcceleration
  exact congrArg (fun L => L (sourceJointTimeDirection n))
    (sourceRealFderiv_periodic (jointSourceCoverVelocity F)
      (TorusCharacters.imaginaryShift m, (0 : ℂ))
      (jointSourceCoverVelocity_spatial_periodic hperiod m) q)
end Ehrhart.EnvelopeGeneralTorusDescent
