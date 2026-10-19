-- Prove2me | solution 1 for Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure.isOpenMap_sourceJointCoverExp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/fdaa60b5-5460-46b2-bd54-129d8c98dce6

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
    IsOpenMap (sourceJointCoverExp (n := n)) := by
  have hid : IsOpenMap
      (fun z : TorusCharacters.LogSpace n => z) := by
    intro s hs
    simpa using hs
  change IsOpenMap (Prod.map
    (fun z : TorusCharacters.LogSpace n => z) Complex.exp)
  exact hid.prodMap Complex.isOpenMap_exp
end Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure
