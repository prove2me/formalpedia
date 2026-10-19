-- Prove2me | solution 1 for CohnElkies.lowerWallisPhaseKernel_abs_le_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/a96cd29b-a1bf-45ae-a250-7a448dd469f2

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
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    |lowerWallisPhaseKernel u t| ≤ |u| + 1 := by
  let q : ℝ := Real.exp (-t)
  have hqpos : 0 < q := by
    try dsimp [q]
    positivity
  have hqone : q ≤ 1 := by
    try dsimp [q]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hone : 0 ≤ 1 - q := by
    linarith
  have hone_le : 1 - q ≤ t := by
    try dsimp [q]
    linarith [Real.add_one_le_exp (-t)]
  have hcos :
      |Real.cos (u * t) - 1| ≤ |u| * t := by
    have h := Real.abs_cos_sub_cos_le (u * t) 0
    simpa [abs_mul, abs_of_pos ht] using! h
  have hqproduct : (1 + t) * q ≤ 1 := by
    calc
      (1 + t) * q ≤ Real.exp t * q := by
        apply mul_le_mul_of_nonneg_right _ hqpos.le
        simpa [add_comm] using! Real.add_one_le_exp t
      _ = 1 := by
        try dsimp [q]
        rw [← Real.exp_add]
        simp
  have hcancel_nonneg : 0 ≤ 1 - q - t * q := by
    nlinarith
  have hcancel_upper : 1 - q - t * q ≤ t ^ 2 := by
    calc
      1 - q - t * q ≤ t * (1 - q) := by
        nlinarith [hone_le]
      _ ≤ t * t :=
        mul_le_mul_of_nonneg_left hone_le ht.le
      _ = t ^ 2 := by
        ring
  have hdecomp :
      (1 - q) * Real.cos (u * t) - t * q =
        (1 - q) * (Real.cos (u * t) - 1) +
          (1 - q - t * q) := by
    ring
  have hsq : 0 < t ^ 2 := sq_pos_of_pos ht
  unfold lowerWallisPhaseKernel
  change
    |((1 - q) * Real.cos (u * t) - t * q) / t ^ 2| ≤
      |u| + 1
  rw [hdecomp, abs_div, abs_of_pos hsq]
  apply (div_le_iff₀ hsq).2
  calc
    |(1 - q) * (Real.cos (u * t) - 1) +
        (1 - q - t * q)| ≤
      |(1 - q) * (Real.cos (u * t) - 1)| +
        |1 - q - t * q| :=
      abs_add_le _ _
    _ = (1 - q) * |Real.cos (u * t) - 1| +
        (1 - q - t * q) := by
      rw [abs_mul, abs_of_nonneg hone,
        abs_of_nonneg hcancel_nonneg]
    _ ≤ (1 - q) * (|u| * t) + t ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hcos hone)
        hcancel_upper
    _ ≤ t * (|u| * t) + t ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hone_le
        (mul_nonneg (abs_nonneg u) ht.le)]
    _ = (|u| + 1) * t ^ 2 := by
      ring
end CohnElkies
