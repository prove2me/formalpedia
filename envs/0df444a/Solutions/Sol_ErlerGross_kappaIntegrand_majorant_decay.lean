-- Prove2me | solution 1 for ErlerGross.kappaIntegrand_majorant_decay
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T13:22:18.277906+00:00
-- url     : https://prove2.me/submissions/23c5e6bf-ac70-44d2-bb56-95de06522ee4

import Mathlib

theorem solution :
    forall kappa : Real,
      Real.pi / (8 * (1 + 2 * Real.cosh (Real.pi * kappa / 2))) <=
        (1 + abs kappa) ^ (-2 : Real) := by
  intro kappa
  let t : Real := abs kappa
  let x : Real := Real.pi * t / 2
  have ht : 0 <= t := by simp [t]
  have hx : 0 <= x := by dsimp [x]; positivity
  have habs : |Real.pi * kappa / 2| = x := by
    dsimp [x, t]
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
  have hpi : 2 < Real.pi := by linarith [Real.pi_gt_three]
  have hlin : 1 + x / 2 <= Real.exp (x / 2) := by
    nlinarith [Real.add_one_le_exp (x / 2)]
  have hexpquad : (1 + x / 2) ^ 2 <= Real.exp x := by
    have he := Real.exp_add (x / 2) (x / 2)
    calc
      (1 + x / 2) ^ 2 <= Real.exp (x / 2) ^ 2 := by nlinarith [hlin]
      _ = Real.exp (x / 2) * Real.exp (x / 2) := by ring
      _ = Real.exp (x / 2 + x / 2) := he.symm
      _ = Real.exp x := by congr 1 <;> ring_nf
  have hpoly : Real.pi / 8 * (1 + t) ^ 2 <= (1 + x / 2) ^ 2 := by
    dsimp [x]
    nlinarith [Real.pi_lt_four, mul_nonneg (sub_nonneg.mpr (le_of_lt hpi)) (sq_nonneg t), mul_nonneg ht Real.pi_pos.le]
  have hcosh : Real.exp x <= 1 + 2 * Real.cosh x := by
    rw [Real.cosh_eq]
    have he : 0 < Real.exp (-x) := Real.exp_pos (-x)
    have he' : 0 < Real.exp x := Real.exp_pos x
    nlinarith
  have hmain : Real.pi * (1 + t) ^ 2 <= 8 * (1 + 2 * Real.cosh x) := by
    have h := hpoly.trans (hexpquad.trans hcosh)
    dsimp [x] at h
    nlinarith [Real.pi_pos]
  have hden : 0 < 8 * (1 + 2 * Real.cosh x) := by positivity
  have hb : 0 < (1 + t) ^ 2 := by positivity
  have hc : Real.cosh (Real.pi * kappa / 2) = Real.cosh x := by
    calc
      Real.cosh (Real.pi * kappa / 2) = Real.cosh |Real.pi * kappa / 2| := (Real.cosh_abs _).symm
      _ = Real.cosh x := congrArg Real.cosh habs
  rw [hc]
  change Real.pi / (8 * (1 + 2 * Real.cosh x)) <= (1 + t) ^ (-2 : Real)
  rw [Real.rpow_neg (by positivity : 0 <= 1 + t) (2 : Real)]
  rw [div_le_iff₀ hden]
  have hmul : Real.pi <= (1 / ((1 + t) ^ 2)) * (8 * (1 + 2 * Real.cosh x)) := by
    calc
      Real.pi = (Real.pi * (1 + t) ^ 2) / ((1 + t) ^ 2) := by field_simp
      _ <= (8 * (1 + 2 * Real.cosh x)) / ((1 + t) ^ 2) := div_le_div_of_nonneg_right hmain hb.le
      _ = (1 / ((1 + t) ^ 2)) * (8 * (1 + 2 * Real.cosh x)) := by field_simp
  simpa [one_div] using hmul