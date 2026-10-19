-- Prove2me | solution 1 for CohnElkies.lowerWallisPhaseKernel_abs_le_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/ac1124e5-8c6a-47a1-8516-f23bc89218dc

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
    (u : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    |lowerWallisPhaseKernel u t| ≤
      1 / t ^ 2 + Real.exp (-t) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let q : ℝ := Real.exp (-t)
  have hqpos : 0 < q := by
    try dsimp [q]
    positivity
  have hqone : q ≤ 1 := by
    try dsimp [q]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hone : 0 ≤ 1 - q := by
    linarith
  have hone_upper : 1 - q ≤ 1 := by
    linarith
  have ht_sq : t ≤ t ^ 2 := by
    nlinarith
  have hsq : 0 < t ^ 2 := sq_pos_of_pos htpos
  unfold lowerWallisPhaseKernel
  change
    |((1 - q) * Real.cos (u * t) - t * q) / t ^ 2| ≤
      1 / t ^ 2 + q
  rw [abs_div, abs_of_pos hsq]
  apply (div_le_iff₀ hsq).2
  calc
    |(1 - q) * Real.cos (u * t) - t * q| ≤
      |(1 - q) * Real.cos (u * t)| + |t * q| :=
      abs_sub _ _
    _ = (1 - q) * |Real.cos (u * t)| + t * q := by
      rw [abs_mul, abs_of_nonneg hone,
        abs_mul, abs_of_pos htpos, abs_of_pos hqpos]
    _ ≤ 1 + t * q := by
      have hcos : |Real.cos (u * t)| ≤ 1 :=
        Real.abs_cos_le_one _
      have hfactor :
          (1 - q) * |Real.cos (u * t)| ≤ 1 := by
        calc
          (1 - q) * |Real.cos (u * t)| ≤
            (1 - q) * 1 :=
            mul_le_mul_of_nonneg_left hcos hone
          _ ≤ 1 := by
            simpa using! hone_upper
      linarith
    _ ≤ 1 + q * t ^ 2 := by
      nlinarith [mul_nonneg hqpos.le
        (sub_nonneg.mpr ht_sq)]
    _ = (1 / t ^ 2 + q) * t ^ 2 := by
      field_simp [htpos.ne']
end CohnElkies
