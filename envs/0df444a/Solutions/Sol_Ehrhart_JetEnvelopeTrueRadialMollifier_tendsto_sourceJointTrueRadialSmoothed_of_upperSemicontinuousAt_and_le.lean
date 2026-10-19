-- Prove2me | solution 1 for Ehrhart.JetEnvelopeTrueRadialMollifier.tendsto_sourceJointTrueRadialSmoothed_of_upperSemicontinuousAt_and_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/ce25c418-e1cc-4622-be63-b28b7318ec3f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeTrueRadialMollifier_eventually_sourceJointTrueRadialSmoothed_le_of_upperSemicontinuousAt

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetEnvelopeTrueRadialMollifier
open Set Filter Function MeasureTheory Metric
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators Topology ENNReal InnerProductSpace Convolution ContDiff
attribute [local instance] Ehrhart.JetEnvelopeTrueRadialMollifier.sourceJointCoverVolume_isAddHaar
namespace Ehrhart.JetEnvelopeTrueRadialMollifier
theorem _root_.solution
    {n : ℕ} {f : SourceJointComplexCover n → ℝ}
    (hf : LocallyIntegrable f
      (volume : Measure (SourceJointComplexCover n)))
    (q : SourceJointComplexCover n)
    (hupper : UpperSemicontinuousAt f q)
    (hlower : ∀ k : ℕ, f q ≤ sourceJointTrueRadialSmoothed f k q) :
    Tendsto (fun k : ℕ => sourceJointTrueRadialSmoothed f k q)
      atTop (𝓝 (f q)) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall
      (fun k => lt_of_lt_of_le hb (hlower k))
  · intro b hb
    have hε : 0 < (b - f q) / 2 := by linarith
    filter_upwards
      [eventually_sourceJointTrueRadialSmoothed_le_of_upperSemicontinuousAt
        hf q hupper hε] with k hk
    linarith
end Ehrhart.JetEnvelopeTrueRadialMollifier
