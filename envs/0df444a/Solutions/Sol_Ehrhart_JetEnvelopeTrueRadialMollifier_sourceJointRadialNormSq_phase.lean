-- Prove2me | solution 1 for Ehrhart.JetEnvelopeTrueRadialMollifier.sourceJointRadialNormSq_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/9daa2861-9a78-4a84-bbc7-72d50d4a107a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    (u : ℂ) (hu : ‖u‖ = 1)
    (q : SourceJointComplexCover n) :
    sourceJointRadialNormSq (u • q) = sourceJointRadialNormSq q := by
  unfold sourceJointRadialNormSq
  change
    (∑ i : Fin n, Complex.normSq (u * q.1 i)) +
      Complex.normSq (u * q.2) =
    (∑ i : Fin n, Complex.normSq (q.1 i)) + Complex.normSq q.2
  simp_rw [normSq_mul_of_norm_one u hu]
end Ehrhart.JetEnvelopeTrueRadialMollifier
