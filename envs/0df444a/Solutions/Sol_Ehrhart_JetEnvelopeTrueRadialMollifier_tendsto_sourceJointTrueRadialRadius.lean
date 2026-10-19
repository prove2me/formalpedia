-- Prove2me | solution 1 for Ehrhart.JetEnvelopeTrueRadialMollifier.tendsto_sourceJointTrueRadialRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/ae84865e-7fa6-4f61-947c-ce1bd5b18d42

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
theorem _root_.solution :
    Tendsto (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  simpa [Nat.cast_add, Nat.cast_one] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
end Ehrhart.JetEnvelopeTrueRadialMollifier
