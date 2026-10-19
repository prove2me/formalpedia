-- Prove2me | solution 1 for Ehrhart.EnvelopeSpatialPeriodicity.jointLogTime_sourceJointSpatialDeckHomeomorph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/1d785c11-91d0-4102-ae92-092567329a17

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.EnvelopeSpatialPeriodicity
open Set Function Filter MeasureTheory
open ActualJetUpperEnvelope JetEnvelopeRightDerivative
open scoped BigOperators Topology
namespace Ehrhart.EnvelopeSpatialPeriodicity
theorem _root_.solution
    {n : ℕ} (m : Fin n → ℤ)
    (q : PositiveJointLogSpace n) :
    jointLogTime (sourceJointSpatialDeckHomeomorph m q) =
      jointLogTime q := by
  rfl
end Ehrhart.EnvelopeSpatialPeriodicity
