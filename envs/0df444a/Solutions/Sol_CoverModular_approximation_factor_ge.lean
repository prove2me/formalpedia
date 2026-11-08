-- Prove2me | solution 1 for CoverModular.approximation_factor_ge
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:02:21.722352+00:00
-- url     : https://prove2.me/submissions/a4c59893-879a-4994-875c-b94f0b6b55f7

import Mathlib

theorem solution (K : ℕ) (hK : 1 ≤ K) :
    (1 - Real.exp (-2)) / 2 ≤ (1 - (1 - 2 / (K : ℝ)) ^ K) / 2 := by
  rcases Nat.lt_or_ge K 2 with h | h
  · have hK1 : K = 1 := by omega
    subst hK1
    have := Real.exp_pos (-2)
    norm_num
    linarith
  · have h2 : (2:ℝ) ≤ (K:ℝ) := by exact_mod_cast h
    have := Real.one_sub_div_pow_le_exp_neg (n := K) (t := 2) h2
    linarith
