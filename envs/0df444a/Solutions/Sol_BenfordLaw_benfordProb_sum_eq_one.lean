-- Prove2me | solution 1 for BenfordLaw.benfordProb_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:43:17.809102+00:00
-- url     : https://prove2.me/submissions/c46e63d5-35e0-4d21-93e0-f29eab8c04ca

import Mathlib
import Definitions.Def_BenfordLaw_Defs
open BenfordLaw

theorem solution (b : ℕ) (hb : 2 ≤ b) :
    ∑ d ∈ Finset.Icc 1 (b - 1), benfordProb b d = 1 := by
  have key : ∀ n : ℕ, ∑ d ∈ Finset.Icc 1 n, benfordProb b d = Real.logb b ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, benfordProb]
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [← Real.logb_mul h1.ne' (by positivity)]
      congr 1
      push_cast
      field_simp
  rw [key, Nat.cast_sub (by omega), Nat.cast_one, sub_add_cancel, Real.logb_self_eq_one]
  exact_mod_cast (by omega : 1 < b)
