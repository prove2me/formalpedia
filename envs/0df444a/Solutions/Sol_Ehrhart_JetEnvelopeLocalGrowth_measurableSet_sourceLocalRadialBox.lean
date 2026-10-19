-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.measurableSet_sourceLocalRadialBox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/a4a03793-f2bb-490c-8381-b7fbd25d6a2e

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
theorem _root_.solution (n : ℕ) (δ : ℝ) :
    MeasurableSet (sourceLocalRadialBox n δ) := by
  exact MeasurableSet.pi Set.countable_univ
    (fun _ _ => measurableSet_Ioo)
end Ehrhart.JetEnvelopeLocalGrowth
