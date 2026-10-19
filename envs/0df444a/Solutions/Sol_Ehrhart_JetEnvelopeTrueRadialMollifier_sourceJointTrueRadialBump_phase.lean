-- Prove2me | solution 1 for Ehrhart.JetEnvelopeTrueRadialMollifier.sourceJointTrueRadialBump_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/5fa4ceee-cce7-49db-811e-1f6d9584e2ca

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeTrueRadialMollifier_sourceJointRadialNormSq_phase

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetEnvelopeTrueRadialMollifier
open Set Filter Function MeasureTheory Metric
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators Topology ENNReal InnerProductSpace Convolution ContDiff
attribute [local instance] Ehrhart.JetEnvelopeTrueRadialMollifier.sourceJointCoverVolume_isAddHaar
namespace Ehrhart.JetEnvelopeTrueRadialMollifier
theorem _root_.solution {n : ℕ}
    (k : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    (q : SourceJointComplexCover n) :
    sourceJointTrueRadialBump n k (u • q) =
      sourceJointTrueRadialBump n k q := by
  simp [sourceJointTrueRadialBump,
    sourceJointRadialNormSq_phase u hu q]
end Ehrhart.JetEnvelopeTrueRadialMollifier
