-- Prove2me | solution 1 for Ehrhart.MonomialDivergence.rayBall_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/4c4ee608-56d5-4153-8514-2d33e7e09aea

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MonomialDivergence
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace Ehrhart.MonomialDivergence
theorem _root_.solution {n : ℕ} (v : Space n)
    (hv : v ≠ 0) (j : ℕ) :
    (volume : Measure (Space n)) (rayBall v j) =
      ENNReal.ofReal ((2 * (‖v‖ / 4)) ^ n) := by
  have hr : 0 < ‖v‖ / 4 :=
    div_pos (norm_pos_iff.mpr hv) (by norm_num)
  unfold rayBall
  simpa using Real.volume_pi_ball ((j : ℝ) • v) hr
end Ehrhart.MonomialDivergence
