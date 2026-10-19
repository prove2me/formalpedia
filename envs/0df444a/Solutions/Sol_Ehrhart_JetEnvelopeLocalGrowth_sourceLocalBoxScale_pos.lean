-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.sourceLocalBoxScale_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/2efa8de2-261d-4db2-97db-946f70ac1b7c

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
theorem _root_.solution {R : ℝ} (hR : 0 < R) :
    0 < sourceLocalBoxScale R := by
  unfold sourceLocalBoxScale
  exact lt_min (by norm_num)
    (div_pos hR (by positivity))
end Ehrhart.JetEnvelopeLocalGrowth
