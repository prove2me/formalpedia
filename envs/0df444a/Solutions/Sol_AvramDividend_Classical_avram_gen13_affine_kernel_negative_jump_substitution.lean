-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen13_affine_kernel_negative_jump_substitution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:23:53.429464+00:00
-- url     : https://prove2.me/submissions/979427d2-0e84-42b8-b013-6f7b1cfb1918

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- Convert a negative jump mark into its positive magnitude in the affine kernel. -/
theorem solution
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    (∫ z in (-1 : ℝ)..(-y), (-1 - y - z) *
      |z| ^ (-(3 / 2 : ℝ))) =
    (∫ r in y..1, (r ^ (-(1 / 2 : ℝ)) -
      (1 + y) * r ^ (-(3 / 2 : ℝ)))) := by
  calc
    (∫ z in (-1 : ℝ)..(-y), (-1 - y - z) * |z| ^ (-(3 / 2 : ℝ))) =
        (∫ r in y..1, (-1 - y - (-r)) * |(-r)| ^ (-(3 / 2 : ℝ))) := by
          simpa using (intervalIntegral.integral_comp_neg
            (a := y) (b := 1)
            (f := fun z : ℝ => (-1 - y - z) * |z| ^ (-(3 / 2 : ℝ)))).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hrint : r ∈ Set.Icc y 1 := by simpa [Set.uIcc_of_le hy1] using hr
      have hrpos : 0 < r := lt_of_lt_of_le hy hrint.1
      have he : -(1 / 2 : ℝ) = (1 : ℝ) + -(3 / 2 : ℝ) := by norm_num
      have hpowers : r ^ (-(1 / 2 : ℝ)) = r * r ^ (-(3 / 2 : ℝ)) := by
        rw [he, Real.rpow_add hrpos, Real.rpow_one]
      simp only [abs_neg, abs_of_pos hrpos]
      rw [hpowers]
      ring
