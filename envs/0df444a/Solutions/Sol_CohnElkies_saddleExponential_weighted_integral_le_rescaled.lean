-- Prove2me | solution 1 for CohnElkies.saddleExponential_weighted_integral_le_rescaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/f5784b0c-6595-4b69-9a50-8114f5f4da85

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integrable_exp_neg_mul_abs
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_le_two_exp_three_abs
import Theorems.Thm_CohnElkies_saddle_integral_exp_neg_mul_abs
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_mul_exp_abs_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {k : ℝ} (hk : 0 < k) :
    (∫ T : ℝ,
      saddleGaussianTailWeight T *
        Real.exp (-k * |T|)) ≤
      2 * max (1 : ℝ) (((k / 6) ^ 3)⁻¹) *
        (2 / (k / 2)) := by
  let s : ℝ := k / 6
  let C : ℝ := max (1 : ℝ) (s ^ 3)⁻¹
  have hs : 0 < s := by
    try dsimp [s]
    positivity
  have hC : 0 ≤ C := by
    try dsimp [C]
    positivity
  have hCone : 1 ≤ C := le_max_left _ _
  have hCinv : (s ^ 3)⁻¹ ≤ C := le_max_right _ _
  have hCproduct : 1 ≤ C * s ^ 3 := by
    calc
      (1 : ℝ) = (s ^ 3)⁻¹ * s ^ 3 := by
        field_simp [hs.ne']
      _ ≤ C * s ^ 3 :=
        mul_le_mul_of_nonneg_right hCinv
          (by positivity)
  have hweight (T : ℝ) :
      saddleGaussianTailWeight T ≤
        C * saddleGaussianTailWeight (s * T) := by
    unfold saddleGaussianTailWeight
    rw [abs_mul, abs_of_pos hs]
    have hcube : 0 ≤ |T| ^ 3 := by positivity
    have hscaled := mul_le_mul_of_nonneg_right
      hCproduct hcube
    nlinarith
  have hpoint (T : ℝ) :
      saddleGaussianTailWeight T *
          Real.exp (-k * |T|) ≤
        (2 * C) * Real.exp (-(k / 2) * |T|) := by
    calc
      saddleGaussianTailWeight T *
          Real.exp (-k * |T|) ≤
        (C * saddleGaussianTailWeight (s * T)) *
          Real.exp (-k * |T|) := by
            exact mul_le_mul_of_nonneg_right
              (hweight T) (Real.exp_pos _).le
      _ ≤ (C * (2 * Real.exp (3 * |s * T|))) *
          Real.exp (-k * |T|) := by
            gcongr
            exact saddleGaussianTailWeight_le_two_exp_three_abs
              (s * T)
      _ = (2 * C) * Real.exp (-(k / 2) * |T|) := by
        have hargument :
            3 * |s * T| + -k * |T| =
              -(k / 2) * |T| := by
          rw [abs_mul, abs_of_pos hs]
          try dsimp [s]
          ring
        calc
          (C * (2 * Real.exp (3 * |s * T|))) *
              Real.exp (-k * |T|) =
            (2 * C) *
              (Real.exp (3 * |s * T|) *
                Real.exp (-k * |T|)) := by ring
          _ = (2 * C) *
              Real.exp (-(k / 2) * |T|) := by
            rw [← Real.exp_add, hargument]
  have hsource :=
    saddleGaussianTailWeight_mul_exp_abs_integrable hk
  have hmajor :=
    (integrable_exp_neg_mul_abs
      (show 0 < k / 2 by positivity)).const_mul (2 * C)
  have hmono := integral_mono_ae hsource hmajor
    (Filter.Eventually.of_forall hpoint)
  calc
    (∫ T : ℝ,
      saddleGaussianTailWeight T *
        Real.exp (-k * |T|)) ≤
      ∫ T : ℝ,
        (2 * C) * Real.exp (-(k / 2) * |T|) := hmono
    _ = 2 * max (1 : ℝ) (((k / 6) ^ 3)⁻¹) *
        (2 / (k / 2)) := by
      rw [MeasureTheory.integral_const_mul,
        saddle_integral_exp_neg_mul_abs
          (show 0 < k / 2 by positivity)]
end CohnElkies
