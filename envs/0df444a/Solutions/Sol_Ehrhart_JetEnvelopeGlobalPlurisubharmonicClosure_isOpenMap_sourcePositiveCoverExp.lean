-- Prove2me | solution 1 for Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure.isOpenMap_sourcePositiveCoverExp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/e7efff27-08d1-417a-9a07-584b2da6c743

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeGlobalPlurisubharmonicClosure_isOpenMap_sourceJointCoverExp
import Theorems.Thm_Ehrhart_JetEnvelopeGlobalPlurisubharmonicClosure_isOpen_sourcePositiveCover

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure
open Set Filter Function MeasureTheory Metric
open ActualJetUpperEnvelope ActualJetPlurisubharmonicEnvelope ActualJetPlurisubharmonicClosure
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators Topology ENNReal InnerProductSpace
namespace Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure
theorem _root_.solution (n : ℕ) :
    IsOpenMap (sourcePositiveCoverExp (n := n)) := by
  let s : Set (SourceJointComplexCover n) :=
    {q | 0 < sourceJointCoverTime q}
  have hs : IsOpen s := isOpen_sourcePositiveCover n
  have hr : IsOpenMap (fun q : s => sourceJointCoverExp q.val) :=
    (isOpenMap_sourceJointCoverExp n).comp hs.isOpenMap_subtype_val
  have hlands : ∀ q : s,
      sourceJointCoverExp q.val ∈ positiveJointDomain n := by
    intro q
    change 1 < Complex.normSq (sourceJointCoverExp q.val).2
    rw [normSq_sourceJointCoverExp]
    simpa using (Real.exp_lt_exp.mpr q.property)
  exact hr.subtype_mk hlands
end Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure
