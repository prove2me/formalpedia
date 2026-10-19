-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.sourceLocalRadialBox_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/5699df5f-4277-492a-b5fd-1a86598d738f

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
    (volume : Measure (Space n))
      (sourceLocalRadialBox n δ) =
        (ENNReal.ofReal (2 * δ)) ^ n := by
  unfold sourceLocalRadialBox
  rw [Real.volume_pi_Ioo]
  simp [sub_neg_eq_add, two_mul]
end Ehrhart.JetEnvelopeLocalGrowth
