-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger169_discount_exponential_Euler_quadratic_cell_all_scales
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:18:36.529769+00:00
-- url     : https://prove2.me/submissions/94e1cc1a-e5ab-4bad-8bad-9daa9b4246c4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gledger145_discount_exponential_Euler_quadratic_cell
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real AvramDividend.Classical
noncomputable section
theorem solution
    (q t δ : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t) (hδ : 0 ≤ δ) :
    |Real.exp (-(q * (t + δ))) - Real.exp (-(q * t)) +
        q * δ * Real.exp (-(q * t))| ≤ (q * δ) ^ 2 := by
  have hu : 0 ≤ q * δ := mul_nonneg hq hδ
  have hrem : |Real.exp (-(q * δ)) - 1 + q * δ| ≤ (q * δ) ^ 2 := by
    by_cases hs : q * δ ≤ 1
    · have h := avram_gledger145_discount_exponential_Euler_quadratic_cell
        q 0 δ hq le_rfl hδ hs
      simpa only [zero_add, mul_zero, neg_zero, Real.exp_zero, mul_one] using h
    · have hge : 1 ≤ q * δ := le_of_not_ge hs
      have hE1 : Real.exp (-(q * δ)) ≤ 1 := by
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
      have hE0 : 0 ≤ Real.exp (-(q * δ)) - 1 + q * δ := by
        nlinarith [Real.add_one_le_exp (-(q * δ))]
      rw [abs_of_nonneg hE0]
      have hquad : 0 ≤ (q * δ) * (q * δ - 1) :=
        mul_nonneg hu (by linarith)
      nlinarith
  have hEpos : 0 ≤ Real.exp (-(q * t)) := (Real.exp_pos _).le
  have hE1 : Real.exp (-(q * t)) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hq ht))
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
      mul_le_mul_of_nonneg_left hrem hEpos
    _ ≤ (q * δ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hE1) (sq_nonneg (q * δ))]
