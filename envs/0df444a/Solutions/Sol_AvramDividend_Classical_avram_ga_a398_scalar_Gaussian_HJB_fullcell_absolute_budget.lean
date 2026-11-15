-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a398_scalar_Gaussian_HJB_fullcell_absolute_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:16:46.38521+00:00
-- url     : https://prove2.me/submissions/e030a5fd-31ba-400e-b98d-7fa959105cdb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

theorem solution
    (M a E δ z u v g : ℝ) (hM : 0 ≤ M) (ha : 0 ≤ a)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (hδ : 0 ≤ δ)
    (hu : |u| ≤ M) (hv : |v| ≤ M) (hg : |g| ≤ M) :
    |E * (u * z + v / 2 * (z^2 - δ * a)) + δ * E * g| ≤
      M * (2 + a) * (|z| + z^2 + δ) := by
  have hd : |z^2 - δ * a| ≤ z^2 + δ * a := by
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg hδ ha]
  have hsub : |u * z + v / 2 * (z^2 - δ * a)| ≤
      M * |z| + M / 2 * (z^2 + δ * a) := by
    calc
      _ ≤ |u * z| + |v / 2 * (z^2 - δ * a)| := abs_add_le _ _
      _ = |u| * |z| + |v| / 2 * |z^2 - δ * a| := by
        rw [abs_mul, abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right hu (abs_nonneg z))
        (mul_le_mul (div_le_div_of_nonneg_right hv (by norm_num))
          hd (abs_nonneg _) (by positivity))
  calc
    |E * (u * z + v / 2 * (z^2 - δ * a)) + δ * E * g|
      ≤ |E * (u * z + v / 2 * (z^2 - δ * a))| + |δ * E * g| :=
        abs_add_le _ _
    _ = E * |u * z + v / 2 * (z^2 - δ * a)| + δ * E * |g| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hE0, abs_of_nonneg hδ]
    _ ≤ M * |z| + M / 2 * (z^2 + δ * a) + δ * M := by
      have hA : 0 ≤ M * |z| + M / 2 * (z^2 + δ * a) := by positivity
      have h1 := mul_le_mul_of_nonneg_left hsub hE0
      have h2 := mul_le_mul_of_nonneg_left hg (mul_nonneg hδ hE0)
      have h3 := mul_le_mul_of_nonneg_right hE1 hA
      have h4 := mul_le_mul_of_nonneg_right hE1 (mul_nonneg hδ hM)
      nlinarith
    _ ≤ M * (2 + a) * (|z| + z^2 + δ) := by
      nlinarith [mul_nonneg hM (abs_nonneg z),
        mul_nonneg hM (sq_nonneg z), mul_nonneg hM hδ,
        mul_nonneg (mul_nonneg hM ha) (abs_nonneg z),
        mul_nonneg (mul_nonneg hM ha) (sq_nonneg z),
        mul_nonneg (mul_nonneg hM ha) hδ]
