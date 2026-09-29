-- Prove2me | solution 1 for BlockCycleRotation.e_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:33:07.32147+00:00
-- url     : https://prove2.me/submissions/3c88533c-cba6-40f9-890c-c7efd8325a59

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

end BlockCycleRotation

open BlockCycleRotation in
/-- `e θ = 1` exactly on the integer multiples of `2π`. -/
theorem solution (θ : ℝ) : e θ = 1 ↔ ∃ n : ℤ, θ = 2 * π * n:= by
  rw [e, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hn' : ((θ : ℝ) : ℂ) * Complex.I = ((2 * π * (n : ℝ) : ℝ) : ℂ) * Complex.I := by
      rw [hn]; push_cast; ring
    have h2 := mul_right_cancel₀ Complex.I_ne_zero hn'
    exact_mod_cast h2
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn]; push_cast; ring⟩
