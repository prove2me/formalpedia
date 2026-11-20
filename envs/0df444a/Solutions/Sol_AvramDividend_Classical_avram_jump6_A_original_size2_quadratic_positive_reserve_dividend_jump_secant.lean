-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_size2_quadratic_positive_reserve_dividend_jump_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:55:17.495208+00:00
-- url     : https://prove2.me/submissions/f3d2ea62-1311-4155-97a6-850ab134b7e8

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
noncomputable section
theorem solution
    (y δ : ℝ) (hy : 0 ≤ y) (hδ : 0 ≤ δ) (hδle : δ ≤ y) :
    δ ≤ (if y < 0 then 0 else 1 + y + y ^ 2) -
      (if y - δ < 0 then 0 else 1 + (y - δ) + (y - δ) ^ 2) := by
  have hy0 : ¬ y < 0 := not_lt_of_ge hy
  have hyδ0 : ¬ y - δ < 0 := not_lt_of_ge (sub_nonneg.mpr hδle)
  simp only [if_neg hy0, if_neg hyδ0]
  have hm : 0 ≤ δ * (2 * y - δ) :=
    mul_nonneg hδ (by linarith)
  nlinarith
