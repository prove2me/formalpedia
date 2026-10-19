-- Prove2me | solution 1 for Ehrhart.MonomialDivergence.rayBall_pairwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/18193619-b5e0-4397-ac20-cfcba4b2ff58

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MonomialDivergence_one_le_abs_cast_sub

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
theorem _root_.solution {n : ℕ} (v : Space n) :
    Pairwise (Function.onFun Disjoint (rayBall v)) := by
  intro i j hij
  apply Metric.ball_disjoint_ball
  change ‖v‖ / 4 + ‖v‖ / 4 ≤
    dist ((i : ℝ) • v) ((j : ℝ) • v)
  have hdist :
      ‖v‖ ≤ dist ((i : ℝ) • v) ((j : ℝ) • v) := by
    rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
    simpa using mul_le_mul_of_nonneg_right
      (one_le_abs_cast_sub hij) (norm_nonneg v)
  calc
    ‖v‖ / 4 + ‖v‖ / 4 ≤ ‖v‖ := by
      linarith [norm_nonneg v]
    _ ≤ dist ((i : ℝ) • v) ((j : ℝ) • v) := hdist
end Ehrhart.MonomialDivergence
