-- Prove2me | solution 1 for Ehrhart.EnvelopeTorusDescent.hasDerivAt_sourceJointTimeEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/828ae405-9ae4-452a-ac6d-227ab815a232

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.EnvelopeTorusDescent
open Set Function Filter MeasureTheory
open JetEnvelopeGlobalPlurisubharmonic EnvelopeSmoothing
open scoped Topology ContDiff
namespace Ehrhart.EnvelopeTorusDescent
theorem _root_.solution
    {n : ℕ}
    (z : TorusCharacters.LogSpace n)
    (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => sourceJointTimeEmbedding z s)
      (sourceJointTimeDirection n) t := by
  unfold sourceJointTimeEmbedding sourceJointTimeDirection
  exact (hasDerivAt_const t z).prodMk
    (Complex.ofRealCLM.hasDerivAt.div_const (2 : ℂ))
end Ehrhart.EnvelopeTorusDescent
