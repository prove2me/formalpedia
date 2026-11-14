-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a202_small_C2_Taylor_remainder_gives_local_Lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:11:25.788424+00:00
-- url     : https://prove2.me/submissions/1f361f2e-5e88-4600-8023-8ba9f405b77c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section

/-- Local second-order Taylor error and compact first/second jet bounds give
a uniform small-increment Lipschitz value estimate on the original source. -/
theorem solution
    (e d j r ε M : ℝ)
    (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hd : |d| ≤ M) (hj : |j| ≤ M)
    (hr : |r| ≤ 1)
    (hTaylor : |e - d * r - j * r^2 / 2| ≤ ε * r^2) :
    |e| ≤ (3 * M / 2 + ε) * |r| := by
  have hsq : r^2 ≤ |r| := by
    have h0 : 0 ≤ |r| := abs_nonneg _
    have hprod : 0 ≤ |r| * (1 - |r|) :=
      mul_nonneg h0 (sub_nonneg.mpr hr)
    nlinarith [sq_abs r]
  have hdMul : |d * r| ≤ M * |r| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hd (abs_nonneg _)
  have hjMul : |j * r^2 / 2| ≤ (M / 2) * r^2 := by
    have heq : |j * r^2 / 2| = (|j| / 2) * r^2 := by
      rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg r),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hj (by norm_num)) (sq_nonneg _)
  have htriple : |e| ≤
      |e - d * r - j * r^2 / 2| + |d * r| + |j * r^2 / 2| := by
    calc
      |e| = |(e - d * r - j * r^2 / 2) +
          (d * r + j * r^2 / 2)| := by congr 1; ring
      _ ≤ |e - d * r - j * r^2 / 2| +
          |d * r + j * r^2 / 2| := abs_add_le _ _
      _ ≤ |e - d * r - j * r^2 / 2| +
          (|d * r| + |j * r^2 / 2|) := by
            have hs : |d * r + j * r^2 / 2| ≤
                |d * r| + |j * r^2 / 2| := abs_add_le _ _
            linarith
      _ = _ := by ring
  have hE := mul_le_mul_of_nonneg_left hsq hε
  have hM2 := mul_le_mul_of_nonneg_left hsq
    (by nlinarith [hM] : 0 ≤ M / 2)
  nlinarith [hTaylor,htriple,hdMul,hjMul]
