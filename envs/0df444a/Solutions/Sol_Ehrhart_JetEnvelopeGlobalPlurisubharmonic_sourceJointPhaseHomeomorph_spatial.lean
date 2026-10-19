-- Prove2me | solution 1 for Ehrhart.JetEnvelopeGlobalPlurisubharmonic.sourceJointPhaseHomeomorph_spatial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/923399c9-28e9-4800-b6b4-e16c446b3835

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
    (sourceJointPhaseHomeomorph u hu q).val.1 = q.val.1 := by
  rfl
end Ehrhart.JetEnvelopeGlobalPlurisubharmonic
