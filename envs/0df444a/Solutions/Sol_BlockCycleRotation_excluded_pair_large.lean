-- Prove2me | solution 1 for BlockCycleRotation.excluded_pair_large
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:26:13.819196+00:00
-- url     : https://prove2.me/submissions/957603bd-6476-45d7-8e4f-4247e9c3b7a4

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **Pairs outside the bulk have large `a`.**  If `d·a·(a+a') > m` then
`2d·a² > m`, so `a > √(m/(2d))`.  This is what makes the truncation of the
series for `C` cost only `O(√(d/m))`. -/
theorem solution {m d a a' : ℕ} (ha' : 1 ≤ a') (haa : a' < a)
    (h : m < d * a * (a + a')) : m < 2 * d * (a * a):= by
  nlinarith
