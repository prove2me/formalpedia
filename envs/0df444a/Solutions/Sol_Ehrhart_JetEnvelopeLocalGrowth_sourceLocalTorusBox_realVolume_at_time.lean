-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.sourceLocalTorusBox_realVolume_at_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/8c98a2a9-4f73-4bc3-9f5e-ddfd86bd59c4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourceLocalBoxRadius_pos
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourceLocalBoxRadius_le_one
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourceLocalTorusBox_realVolume

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
    (n : ℕ) {R t : ℝ}
    (hR : 0 < R) (ht : 0 ≤ t) :
    (sourceTorusBaseMeasure n).real
      (sourceLocalTorusBox n (sourceLocalBoxRadius R t)) =
        sourceLocalBallVolumeConstant n R *
          Real.exp (-(n : ℝ) * t) := by
  rw [sourceLocalTorusBox_realVolume n
    (sourceLocalBoxRadius_pos hR t).le
    (sourceLocalBoxRadius_le_one hR ht)]
  unfold sourceLocalBoxRadius sourceLocalBallVolumeConstant
  have hexp :
      Real.exp (-t / 2) ^ (2 * n) =
        Real.exp (-(n : ℝ) * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc
    (2 * (sourceLocalBoxScale R * Real.exp (-t / 2))) ^ n *
        (sourceLocalBoxScale R * Real.exp (-t / 2)) ^ n =
      2 ^ n * sourceLocalBoxScale R ^ (2 * n) *
        Real.exp (-t / 2) ^ (2 * n) := by
      simp only [mul_pow,
        show 2 * n = n + n by omega, pow_add]
      ring
    _ = 2 ^ n * sourceLocalBoxScale R ^ (2 * n) *
        Real.exp (-(n : ℝ) * t) := by rw [hexp]
end Ehrhart.JetEnvelopeLocalGrowth
