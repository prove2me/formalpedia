-- Prove2me | solution 1 for BlockCycleRotation.error_per_divisor_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:30:19.713307+00:00
-- url     : https://prove2.me/submissions/301cc12e-74ff-4557-a03e-643bac84c0f1

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
/-- The per-divisor error `(n/d)^{3/2}·√d` is `n^{3/2}/d`, hence at most
`n^{3/2}`. -/
theorem solution {n d : ℕ} (hn : 0 < n) (hd : d ∈ n.divisors) :
    ((n / d : ℕ) : ℝ) ^ (3 / 2 : ℝ) * (d : ℝ) ^ ((1 : ℝ) / 2)
      ≤ (n : ℝ) ^ (3 / 2 : ℝ):= by
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd0
  have hnR : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hcast : ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) := Nat.cast_div hdn (by positivity)
  rw [hcast, Real.div_rpow hnR (by positivity), div_mul_eq_mul_div,
    div_le_iff₀ (by positivity)]
  have hexp : (d : ℝ) ^ ((1 : ℝ) / 2) ≤ (d : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hdR (by norm_num)
  have hn32 : (0 : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by positivity
  nlinarith [hexp, hn32]
