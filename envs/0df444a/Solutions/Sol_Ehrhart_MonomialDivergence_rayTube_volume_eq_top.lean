-- Prove2me | solution 1 for Ehrhart.MonomialDivergence.rayTube_volume_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/4473d174-01f5-4b9a-b771-7e4daf2b99c3

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MonomialDivergence_rayBall_pairwise_disjoint
import Theorems.Thm_Ehrhart_MonomialDivergence_rayBall_volume

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
theorem _root_.solution {n : ℕ}
    (v : Space n) (hv : v ≠ 0) :
    (volume : Measure (Space n)) (rayTube v) = ⊤ := by
  unfold rayTube
  rw [measure_iUnion (rayBall_pairwise_disjoint v)
    (fun j => (Metric.isOpen_ball.measurableSet :
      MeasurableSet (rayBall v j)))]
  simp_rw [rayBall_volume v hv]
  apply ENNReal.tsum_const_eq_top_of_ne_zero
  have hpositive : 0 < (2 * (‖v‖ / 4)) ^ n := by
    exact pow_pos (mul_pos (by norm_num)
      (div_pos (norm_pos_iff.mpr hv) (by norm_num))) n
  exact (ENNReal.ofReal_pos.mpr hpositive).ne'
end Ehrhart.MonomialDivergence
