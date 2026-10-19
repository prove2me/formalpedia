-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.sourceLocalAngularBox_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/02566c59-fe11-4e61-b2f3-1dc563d2a158

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourcePositiveAngularArc_haarMeasure

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
theorem _root_.solution
    (n : ℕ) {δ : ℝ} (hδ : δ ≤ 1) :
    WeightedTorusHilbert.angularMeasure n
      (sourceLocalAngularBox n δ) =
        (ENNReal.ofReal δ) ^ n := by
  change
    (Measure.pi (fun _ : Fin n => AddCircle.haarAddCircle))
      (Set.univ.pi fun _ : Fin n => sourcePositiveAngularArc δ) = _
  rw [Measure.pi_pi]
  simp [sourcePositiveAngularArc_haarMeasure hδ]
end Ehrhart.JetEnvelopeLocalGrowth
