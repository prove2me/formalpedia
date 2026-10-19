-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.sourceLocalTorusBox_measure_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/eca89e9c-3fd2-4a78-9ea1-9f6e82d3a4e9

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourceLocalTorusBox_volume

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
    sourceTorusBaseMeasure n (sourceLocalTorusBox n δ) ≠ ⊤ := by
  rw [sourceLocalTorusBox_volume n hδ]
  finiteness
end Ehrhart.JetEnvelopeLocalGrowth
