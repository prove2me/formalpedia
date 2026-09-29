-- Prove2me | solution 1 for BlockCycleRotation.sum_div_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:30:08.010621+00:00
-- url     : https://prove2.me/submissions/06357caf-1ce1-4f51-91ef-99419d3ec346

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
/-- **The main terms sum to `C·n²·∑_{d∣n} 1/d²`.** -/
theorem solution {n : ℕ} (hn : 0 < n) (K : ℝ) :
    ∑ d ∈ n.divisors, K * (((n / d : ℕ) : ℝ)) ^ 2
      = K * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2:= by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hcast : ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) :=
    Nat.cast_div hdn (by positivity)
  rw [hcast]
  field_simp
