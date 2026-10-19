-- Prove2me | solution 1 for Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure.continuous_sourcePositiveCoverExp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/1482f3e1-eae1-44fc-9ce0-4a5a2e4c8c26

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    Continuous (sourcePositiveCoverExp (n := n)) := by
  apply Continuous.subtype_mk
  exact (continuous_sourceJointCoverExp n).comp
    continuous_subtype_val
end Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure
