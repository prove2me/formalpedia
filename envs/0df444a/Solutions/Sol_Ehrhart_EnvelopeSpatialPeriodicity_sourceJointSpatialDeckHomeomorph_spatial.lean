-- Prove2me | solution 1 for Ehrhart.EnvelopeSpatialPeriodicity.sourceJointSpatialDeckHomeomorph_spatial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/1e4f9f9c-8d20-434d-93be-5d36daccd5c2

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
    (sourceJointSpatialDeckHomeomorph m q).val.1 =
      q.val.1 + TorusCharacters.imaginaryShift m := by
  rfl
end Ehrhart.EnvelopeSpatialPeriodicity
