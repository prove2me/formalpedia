-- Prove2me | solution 1 for Ehrhart.BodyScale.canonicalScale_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/bed8b9fb-801a-4448-8904-4895fc964619

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BodyScale
open Set MeasureTheory
namespace Ehrhart.BodyScale
theorem _root_.solution {n : ℕ} (hn : 0 < n)
    (K : CenteredBody n) :
    canonicalScale K ^ n =
      (n.factorial : ℝ) * normalizedVolume K.carrier := by
  unfold canonicalScale
  exact Real.rpow_inv_natCast_pow
    (factorial_mul_volume_pos K).le (Nat.ne_of_gt hn)
end Ehrhart.BodyScale
