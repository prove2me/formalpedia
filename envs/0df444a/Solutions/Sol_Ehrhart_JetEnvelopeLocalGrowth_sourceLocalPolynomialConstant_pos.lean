-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.sourceLocalPolynomialConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/6c98151c-1307-489c-adbc-00489e94c027

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
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n) :
    0 < sourceLocalPolynomialConstant K := by
  unfold sourceLocalPolynomialConstant
  exact mul_pos
    (GlobalBergmanKernelBound.globalKernelPolynomialConstant_pos K)
    (by have hv := K.volume_pos; linarith)
end Ehrhart.JetEnvelopeLocalGrowth
