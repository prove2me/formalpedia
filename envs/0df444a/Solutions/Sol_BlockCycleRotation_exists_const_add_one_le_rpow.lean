-- Prove2me | solution 1 for BlockCycleRotation.exists_const_add_one_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:42:16.735086+00:00
-- url     : https://prove2.me/submissions/9fa01963-dd67-4239-91de-56413e658ef8

import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_exists_const_add_one_le
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

/-- `(p^k)^ε = (p^ε)^k`. -/
theorem natPow_rpow {p : ℕ} (hp : 0 < p) (k : ℕ) (ε : ℝ) :
    (((p ^ k : ℕ) : ℝ)) ^ ε = (((p : ℝ)) ^ ε) ^ k := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  push_cast
  rw [← Real.rpow_natCast ((p : ℝ)) k, ← Real.rpow_mul hp0, mul_comm,
    Real.rpow_mul hp0, Real.rpow_natCast]

end BlockCycleRotation

open BlockCycleRotation in
/-- **Small primes cost a constant.**  For `p ≥ 2` and `ε > 0`, `k + 1` is at most
`C · (p^k)^ε` with `C` depending only on `ε`. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, 2 ≤ p → ∀ k : ℕ,
      ((k : ℝ) + 1) ≤ C * (((p ^ k : ℕ) : ℝ)) ^ ε:= by
  have h2 : (1 : ℝ) < (2 : ℝ) ^ ε := by
    apply Real.one_lt_rpow_iff_of_pos (by norm_num) |>.2
    exact Or.inl ⟨by norm_num, hε⟩
  obtain ⟨C, hC1, hC⟩ := exists_const_add_one_le h2
  refine ⟨C, hC1, fun p hp k => ?_⟩
  have hp0 : 0 < p := by omega
  rw [natPow_rpow hp0 k ε]
  refine (hC k).trans ?_
  have hple : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hrp : (2 : ℝ) ^ ε ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num) hple hε.le
  have hmono : ((2 : ℝ) ^ ε) ^ k ≤ ((p : ℝ) ^ ε) ^ k :=
    pow_le_pow_left₀ (by positivity) hrp k
  exact mul_le_mul_of_nonneg_left hmono (by linarith)
