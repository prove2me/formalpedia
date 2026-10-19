-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.isOpen_sourceLocalJointRegion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/4cb3f886-5872-4b98-a848-7f53bda84147

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetEnvelopeLocalGrowth
open Set Filter MeasureTheory Module Metric Asymptotics
open ActualJetUpperEnvelope JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative
open scoped BigOperators Topology ENNReal InnerProductSpace
universe u v
namespace Ehrhart.JetEnvelopeLocalGrowth
theorem _root_.solution {n : ℕ}
    (p : TorusCharacters.LogSpace n) (R : ℝ) :
    IsOpen (sourceLocalJointRegion p R) := by
  unfold sourceLocalJointRegion
  have htime : Continuous (jointLogTime (n := n)) :=
    continuous_jointLogTime n
  exact isOpen_lt (by fun_prop) (by fun_prop)
end Ehrhart.JetEnvelopeLocalGrowth
