-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.sourceLocalTorusBox_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/7ffaefe9-ec04-4ab4-b342-0843cb0504c6

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourceLocalRadialBox_volume
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourceLocalAngularBox_volume

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
    sourceTorusBaseMeasure n (sourceLocalTorusBox n δ) =
      (ENNReal.ofReal (2 * δ)) ^ n *
        (ENNReal.ofReal δ) ^ n := by
  unfold sourceTorusBaseMeasure sourceLocalTorusBox
  rw [Measure.prod_prod,
    sourceLocalRadialBox_volume,
    sourceLocalAngularBox_volume n hδ]
end Ehrhart.JetEnvelopeLocalGrowth
