-- Prove2me | solution 1 for CohnElkies.lowerWallisRegularizedPhaseKernel_abs_le_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/5a6756be-1edf-493a-92be-e64aa8457069

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {a : ℝ} (hazero : 0 ≤ a)
    (u : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    |lowerWallisRegularizedPhaseKernel a u t| ≤
      1 / t ^ 2 + Real.exp (-t) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let q : ℝ := Real.exp (-t)
  let r : ℝ := Real.exp (-a * t)
  have hqpos : 0 < q := by
    try dsimp [q]
    positivity
  have hqone : q ≤ 1 := by
    try dsimp [q]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hrpos : 0 < r := by
    try dsimp [r]
    positivity
  have hrone : r ≤ 1 := by
    try dsimp [r]
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hazero htpos.le]
  have hqnonneg : 0 ≤ 1 - q := by linarith
  have hsq : 0 < t ^ 2 := sq_pos_of_pos htpos
  have htsq : t ≤ t ^ 2 := by nlinarith
  unfold lowerWallisRegularizedPhaseKernel
  change
    |((1 - q) * r * Real.cos (u * t) - t * q) /
      t ^ 2| ≤ 1 / t ^ 2 + q
  rw [abs_div, abs_of_pos hsq]
  apply (div_le_iff₀ hsq).2
  calc
    |(1 - q) * r * Real.cos (u * t) - t * q| ≤
        |(1 - q) * r * Real.cos (u * t)| + |t * q| :=
      abs_sub _ _
    _ = (1 - q) * r * |Real.cos (u * t)| + t * q := by
      rw [abs_mul, abs_mul, abs_of_nonneg hqnonneg,
        abs_of_pos hrpos, abs_mul, abs_of_pos htpos,
        abs_of_pos hqpos]
    _ ≤ 1 + t * q := by
      have hcos := Real.abs_cos_le_one (u * t)
      have hfirst : (1 - q) * r ≤ 1 := by
        calc
          (1 - q) * r ≤ (1 - q) * 1 :=
            mul_le_mul_of_nonneg_left hrone hqnonneg
          _ ≤ 1 := by linarith
      have hfactor : 0 ≤ (1 - q) * r :=
        mul_nonneg hqnonneg hrpos.le
      nlinarith [mul_le_mul_of_nonneg_left hcos hfactor]
    _ ≤ 1 + q * t ^ 2 := by
      nlinarith [mul_nonneg hqpos.le (sub_nonneg.mpr htsq)]
    _ = (1 / t ^ 2 + q) * t ^ 2 := by
      field_simp [htpos.ne']
end CohnElkies
