-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.measurableSet_sourceLocalTorusBox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/d7f1e006-1eb2-4ee0-8606-601f84840079

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_measurableSet_sourceLocalRadialBox
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_measurableSet_sourceLocalAngularBox

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
theorem _root_.solution (n : ℕ) (δ : ℝ) :
    MeasurableSet (sourceLocalTorusBox n δ) :=
  (measurableSet_sourceLocalRadialBox n δ).prod
    (measurableSet_sourceLocalAngularBox n δ)
end Ehrhart.JetEnvelopeLocalGrowth
