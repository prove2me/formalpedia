-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.sourceLocalTorusBox_realVolume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/ab246c99-56e6-4915-9d8f-882242eb6754

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
    (n : ℕ) {δ : ℝ} (hδnonneg : 0 ≤ δ) (hδ : δ ≤ 1) :
    (sourceTorusBaseMeasure n).real (sourceLocalTorusBox n δ) =
      (2 * δ) ^ n * δ ^ n := by
  change
    (sourceTorusBaseMeasure n (sourceLocalTorusBox n δ)).toReal = _
  rw [sourceLocalTorusBox_volume n hδ,
    ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * δ),
    ENNReal.toReal_ofReal hδnonneg]
end Ehrhart.JetEnvelopeLocalGrowth
