-- Prove2me | solution 1 for Ehrhart.EnvelopeGeneralTorusDescent.jointSourceTorusVelocity_eq_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/54193d26-f0f2-482d-a92c-2cdc6d9a0029

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
    (F : SourceJointComplexCover n → ℝ)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) :
    jointSourceTorusVelocity F t q =
      jointSourceCoverVelocity F
        (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t) := by
  rfl
end Ehrhart.EnvelopeGeneralTorusDescent
