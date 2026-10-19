-- Prove2me | solution 1 for Ehrhart.JetEnvelopeTrueRadialMollifier.sourceJointTrueRadialMollifier_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/8da8a2fa-af5b-4cee-adea-5ef8a1bf1827

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeTrueRadialMollifier_sourceJointTrueRadialBump_phase

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
    sourceJointTrueRadialMollifier n k (u • q) =
      sourceJointTrueRadialMollifier n k q := by
  simp [sourceJointTrueRadialMollifier,
    sourceJointTrueRadialBump_phase k u hu q]
end Ehrhart.JetEnvelopeTrueRadialMollifier
