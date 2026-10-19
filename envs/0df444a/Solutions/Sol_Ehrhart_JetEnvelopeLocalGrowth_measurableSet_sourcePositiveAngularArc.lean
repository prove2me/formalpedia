-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.measurableSet_sourcePositiveAngularArc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/678187e5-5ae0-425c-9490-2b243e684a25

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
theorem _root_.solution (δ : ℝ) :
    MeasurableSet (sourcePositiveAngularArc δ) := by
  have hrepr : Measurable
      (fun θ : UnitAddCircle =>
        ((AddCircle.equivIoc 1 0 θ).1 : ℝ)) :=
    measurable_subtype_coe.comp
      (AddCircle.measurableEquivIoc 1 0).measurable
  exact hrepr measurableSet_Iio
end Ehrhart.JetEnvelopeLocalGrowth
