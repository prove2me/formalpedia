-- Prove2me | solution 1 for Ehrhart.EnvelopeSpatialPeriodicity.sourcePositiveJointTimePoint_spatial_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/cf555ac7-a751-429f-95b8-f2171847d69d

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
    {n : ℕ}
    (z : TorusCharacters.LogSpace n)
    (t : ℝ) (ht : 0 < t)
    (m : Fin n → ℤ) :
    sourcePositiveJointTimePoint
        (z + TorusCharacters.imaginaryShift m) t ht =
      sourceJointSpatialDeckHomeomorph m
        (sourcePositiveJointTimePoint z t ht) := by
  apply Subtype.ext
  rfl
end Ehrhart.EnvelopeSpatialPeriodicity
