-- Prove2me | solution 1 for CohnElkies.saddle_cubic_translation_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/9250da38-9f28-4df6-8e3b-758d899a5cd8

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddle_abs_sq_le_add_cube

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (u T : ℝ) (A B C : ℂ)
    (hA : ‖A‖ ≤ 3 * (1 + |u|) ^ 2)
    (hB : ‖B‖ ≤ 3 * (1 + |u|) ^ 2)
    (hC : ‖C‖ ≤ 1) :
    ‖(T : ℂ) * A + (T : ℂ) ^ 2 * B +
        C * (T : ℂ) ^ 3‖ ≤
      9 * (1 + |u|) ^ 2 * (|T| + |T| ^ 3) := by
  let H : ℝ := (1 + |u|) ^ 2
  let S : ℝ := |T| + |T| ^ 3
  have hH : 1 ≤ H := by
    try dsimp [H]
    nlinarith [abs_nonneg u, sq_nonneg |u|]
  have hS : 0 ≤ S := by
    try dsimp [S]
    positivity
  have hT : |T| ≤ S := by
    try dsimp [S]
    nlinarith [pow_nonneg (abs_nonneg T) 3]
  have hT2 : |T| ^ 2 ≤ S := by
    exact saddle_abs_sq_le_add_cube T
  have hT3 : |T| ^ 3 ≤ S := by
    try dsimp [S]
    linarith [abs_nonneg T]
  have hfirst :
      ‖(T : ℂ) * A‖ ≤ |T| * (3 * H) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hA (abs_nonneg T)
  have hsecond :
      ‖(T : ℂ) ^ 2 * B‖ ≤ |T| ^ 2 * (3 * H) := by
    rw [norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hB
      (sq_nonneg |T|)
  have hthird :
      ‖C * (T : ℂ) ^ 3‖ ≤ |T| ^ 3 := by
    rw [norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_right hC
      (pow_nonneg (abs_nonneg T) 3)]
  have hfirst' : |T| * (3 * H) ≤ 3 * H * S := by
    nlinarith [mul_le_mul_of_nonneg_left hT
      (show 0 ≤ 3 * H by positivity)]
  have hsecond' : |T| ^ 2 * (3 * H) ≤ 3 * H * S := by
    nlinarith [mul_le_mul_of_nonneg_left hT2
      (show 0 ≤ 3 * H by positivity)]
  have hthird' : |T| ^ 3 ≤ H * S := by
    have hraise : S ≤ H * S := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hH) hS]
    exact hT3.trans hraise
  calc
    ‖(T : ℂ) * A + (T : ℂ) ^ 2 * B +
        C * (T : ℂ) ^ 3‖ ≤
      ‖(T : ℂ) * A + (T : ℂ) ^ 2 * B‖ +
        ‖C * (T : ℂ) ^ 3‖ :=
      norm_add_le _ _
    _ ≤ (‖(T : ℂ) * A‖ + ‖(T : ℂ) ^ 2 * B‖) +
        ‖C * (T : ℂ) ^ 3‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (|T| * (3 * H) + |T| ^ 2 * (3 * H)) +
        |T| ^ 3 := by
      gcongr
    _ ≤ 9 * H * S := by
      nlinarith [mul_nonneg (show 0 ≤ H by positivity) hS]
    _ = 9 * (1 + |u|) ^ 2 * (|T| + |T| ^ 3) := by
      rfl
end CohnElkies
