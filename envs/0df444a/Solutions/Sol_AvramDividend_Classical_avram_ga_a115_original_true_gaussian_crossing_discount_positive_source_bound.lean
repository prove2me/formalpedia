-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a115_original_true_gaussian_crossing_discount_positive_source_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:01:27.659107+00:00
-- url     : https://prove2.me/submissions/abea3534-0d7e-44c1-9431-8efadd8cb30b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Discounting the truly stopped original Gaussian crossing-cell source cannot increase its positive spatial error plus HJB compensation. -/
theorem solution
    (q : ℝ) (hq : 0 ≤ q) (ρ : ℝ≥0) (a h : ℝ) :
    max (Real.exp (-(q * (ρ : ℝ))) * a - h) 0 ≤
      |a| + |h| := by
  have hClock : 0 ≤ q * (ρ : ℝ) :=
    mul_nonneg hq ρ.property
  have hE : Real.exp (-(q * (ρ : ℝ))) ≤ 1 :=
    (Real.exp_le_one_iff).2 (neg_nonpos.mpr hClock)
  have hEpos : 0 ≤ Real.exp (-(q * (ρ : ℝ))) :=
    (Real.exp_pos _).le
  calc
    max (Real.exp (-(q * (ρ : ℝ))) * a - h) 0 ≤
        |Real.exp (-(q * (ρ : ℝ))) * a| + |h| := by
      apply max_le
      · linarith [le_abs_self (Real.exp (-(q * (ρ : ℝ))) * a),
          neg_le_abs h]
      · linarith [abs_nonneg (Real.exp (-(q * (ρ : ℝ))) * a),
          abs_nonneg h]
    _ = Real.exp (-(q * (ρ : ℝ))) * |a| + |h| := by
      rw [abs_mul, abs_of_nonneg hEpos]
    _ ≤ |a| + |h| := by
      linarith [mul_le_mul_of_nonneg_right hE (abs_nonneg a)]
