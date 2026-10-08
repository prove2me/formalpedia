-- Prove2me | solution 1 for CongestionPoA.AsymSum.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-04T17:44:46.835673+00:00
-- url     : https://prove2.me/submissions/535144e1-946f-4322-ab49-b7f5aa3125ab

import Mathlib

set_option autoImplicit false

theorem solution (α β : ℕ) :
    (β : ℝ) * ((α : ℝ) + 1) ≤
      (1 / 3 : ℝ) * (α : ℝ) ^ 2 + (5 / 3 : ℝ) * (β : ℝ) ^ 2 := by
  rcases lt_or_ge β 2 with hβ | hβ
  · interval_cases β
    · simp
    · rcases lt_or_ge α 2 with hα | hα
      · interval_cases α <;> norm_num
      · have hα' : (2 : ℝ) ≤ α := by exact_mod_cast hα
        norm_num only [Nat.cast_one, one_mul, one_pow] at *
        nlinarith [sq_nonneg ((α : ℝ) - 2)]
  · have hβ' : (2 : ℝ) ≤ β := by exact_mod_cast hβ
    have hβ0 : (0 : ℝ) ≤ β := Nat.cast_nonneg β
    have hprod : 0 ≤ (β : ℝ) * ((β : ℝ) - 2) :=
      mul_nonneg hβ0 (sub_nonneg.mpr hβ')
    nlinarith [sq_nonneg ((α : ℝ) - (3 / 2 : ℝ) * β)]
