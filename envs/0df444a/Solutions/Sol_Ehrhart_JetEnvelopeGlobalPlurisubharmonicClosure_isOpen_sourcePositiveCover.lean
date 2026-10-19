-- Prove2me | solution 1 for Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure.isOpen_sourcePositiveCover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/1547cf08-fc71-486f-9735-3626013e0cc4

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
    IsOpen
      {q : SourceJointComplexCover n | 0 < sourceJointCoverTime q} := by
  exact isOpen_Ioi.preimage (continuous_sourceJointCoverTime n)
end Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure
