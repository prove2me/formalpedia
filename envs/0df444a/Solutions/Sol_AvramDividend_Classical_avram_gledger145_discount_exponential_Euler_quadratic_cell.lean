-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger145_discount_exponential_Euler_quadratic_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:56:34.52926+00:00
-- url     : https://prove2.me/submissions/ebed5ec8-59eb-44ee-8898-393682dabfe1

import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section
theorem solution
    (q t δ : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hδ : 0 ≤ δ) (hsmall : q * δ ≤ 1) :
    |Real.exp (-(q * (t + δ))) - Real.exp (-(q * t)) +
        q * δ * Real.exp (-(q * t))| ≤ (q * δ) ^ 2 := by
  have hqd : 0 ≤ q * δ := mul_nonneg hq hδ
  have hx : |-(q * δ)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg hqd]
    exact hsmall
  have hTaylor := Real.abs_exp_sub_one_sub_id_le hx
  have heq : Real.exp (-(q * δ)) - 1 - (-(q * δ)) =
      Real.exp (-(q * δ)) - 1 + q * δ := by ring
  rw [heq] at hTaylor
  have hT : |Real.exp (-(q * δ)) - 1 + q * δ| ≤ (q * δ) ^ 2 := by
    nlinarith [hTaylor]
  have hEpos : 0 ≤ Real.exp (-(q * t)) := (Real.exp_pos _).le
  have hE1 : Real.exp (-(q * t)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (mul_nonneg hq ht)
  have hexp : Real.exp (-(q * (t + δ))) =
      Real.exp (-(q * t)) * Real.exp (-(q * δ)) := by
    calc
      Real.exp (-(q * (t + δ))) =
          Real.exp (-(q * t) + -(q * δ)) := by congr 1; ring
      _ = _ := Real.exp_add _ _
  have hfactor :
      Real.exp (-(q * (t + δ))) - Real.exp (-(q * t)) +
          q * δ * Real.exp (-(q * t)) =
        Real.exp (-(q * t)) * (Real.exp (-(q * δ)) - 1 + q * δ) := by
    rw [hexp]
    ring
  calc
    |Real.exp (-(q * (t + δ))) - Real.exp (-(q * t)) +
        q * δ * Real.exp (-(q * t))| =
        Real.exp (-(q * t)) * |Real.exp (-(q * δ)) - 1 + q * δ| := by
          rw [hfactor, abs_mul, abs_of_nonneg hEpos]
    _ ≤ Real.exp (-(q * t)) * (q * δ) ^ 2 :=
      mul_le_mul_of_nonneg_left hT hEpos
    _ ≤ (q * δ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hE1) (sq_nonneg (q * δ))]
