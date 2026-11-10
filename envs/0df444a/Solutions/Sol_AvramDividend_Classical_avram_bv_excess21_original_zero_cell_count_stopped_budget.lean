-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_excess21_original_zero_cell_count_stopped_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T21:34:52.820234+00:00
-- url     : https://prove2.me/submissions/045e311f-16df-403e-8801-4486a060ebba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess20_original_zero_cell_discount_compensator_ceiling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem solution
    (q rate w0 cash s t : ℝ) (k : ℕ)
    (hq : 0 < q) (hrate : 0 ≤ rate) (hw0 : 0 ≤ w0)
    (hst : s ≤ t)
    (hNoJump : k = 0 → cash ≤ (q + rate) * w0 *
      ((Real.exp (-(q * s)) - Real.exp (-(q * t))) / q))
    (hJump : k ≠ 0 → cash ≤
      (q + rate) * w0 * Real.exp (-(q * s)) * (t - s)) :
    let Err : ℝ := if k = 0 then 0 else
      Real.exp (-(q * s)) * w0 * ((k : ℝ) - 1) +
        q * w0 * Real.exp (-(q * s)) * (t - s)
    0 ≤ Err ∧
      cash + (if k = 0 then Real.exp (-(q * t)) * w0 else 0) -
        Real.exp (-(q * s)) * w0 ≤
      -Real.exp (-(q * s)) * w0 *
        ((k : ℝ) - rate * (t - s)) + Err := by
  dsimp only
  constructor
  · by_cases hk : k = 0
    · simp [hk]
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
      simp only [if_neg hk]
      have ha : 0 ≤ Real.exp (-(q * s)) * w0 * ((k : ℝ) - 1) :=
        mul_nonneg (mul_nonneg (le_of_lt (Real.exp_pos _)) hw0)
          (sub_nonneg.mpr hk1)
      have hb : 0 ≤ q * w0 * Real.exp (-(q * s)) * (t - s) :=
        mul_nonneg
          (mul_nonneg (mul_nonneg (le_of_lt hq) hw0)
            (le_of_lt (Real.exp_pos _))) (sub_nonneg.mpr hst)
      linarith
  · by_cases hk : k = 0
    · subst k
      have h := avram_bv_excess20_original_zero_cell_discount_compensator_ceiling
        q rate w0 cash s t hq hrate hw0 hst (hNoJump rfl)
      simp only [if_pos rfl, Nat.cast_zero, if_true]
      convert h using 1 <;> ring
    · have hc := hJump hk
      simp only [if_neg hk]
      nlinarith [hc]
