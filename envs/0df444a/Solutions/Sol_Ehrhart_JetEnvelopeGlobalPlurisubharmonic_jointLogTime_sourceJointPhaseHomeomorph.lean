-- Prove2me | solution 1 for Ehrhart.JetEnvelopeGlobalPlurisubharmonic.jointLogTime_sourceJointPhaseHomeomorph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/14933e14-d836-4206-853a-59ae2c22fd25

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetEnvelopeGlobalPlurisubharmonic
open Set Filter MeasureTheory Metric
open ActualJetUpperEnvelope JetEnvelopeRightDerivative
open scoped BigOperators Topology ENNReal InnerProductSpace
namespace Ehrhart.JetEnvelopeGlobalPlurisubharmonic
theorem _root_.solution {n : ℕ}
    (u : ℂ) (hu : ‖u‖ = 1)
    (q : PositiveJointLogSpace n) :
    jointLogTime (sourceJointPhaseHomeomorph u hu q) =
      jointLogTime q := by
  change Real.log (Complex.normSq (u * q.val.2)) =
    Real.log (Complex.normSq q.val.2)
  rw [normSq_mul_of_norm_one u hu]
end Ehrhart.JetEnvelopeGlobalPlurisubharmonic
