-- Prove2me | solution 1 for Eight.one_le_logb
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:30:55.899203+00:00
-- url     : https://prove2.me/submissions/4ef5f313-a1dc-471f-9961-94202f918bb9

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false

theorem solution {lam : ℕ} (hl : 1 ≤ lam) : (1 : ℝ) ≤ Real.logb 2 (2 * lam) := by
  have h : (2 : ℝ) ≤ 2 * lam := by
    exact_mod_cast Nat.mul_le_mul_left 2 hl
  calc
    (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
    _ ≤ Real.logb 2 (2 * lam) :=
      Real.logb_le_logb_of_le (by norm_num) (by norm_num) h
