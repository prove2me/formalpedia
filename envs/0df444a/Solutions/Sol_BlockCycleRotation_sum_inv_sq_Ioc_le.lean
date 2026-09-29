-- Prove2me | solution 1 for BlockCycleRotation.sum_inv_sq_Ioc_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:28:17.50673+00:00
-- url     : https://prove2.me/submissions/007de7d7-c035-46ba-b64d-6cad8cb651d4

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
/-- Telescoping: `∑_{N < a ≤ M} 1/a² ≤ 1/N - 1/M`. -/
theorem solution {N : ℕ} (hN : 0 < N) :
    ∀ M, N ≤ M → ∑ a ∈ Finset.Ioc N M, 1 / ((a : ℝ) ^ 2) ≤ 1 / (N : ℝ) - 1 / (M : ℝ):= by
  intro M hNM
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    rw [Finset.sum_Ioc_succ_top hNM]
    have hM : (1 : ℝ) ≤ (M : ℝ) := by
      have h : 1 ≤ M := by omega
      exact_mod_cast h
    have hstep : 1 / (((M + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / (M : ℝ) - 1 / (((M + 1 : ℕ) : ℝ)) := by
      push_cast
      have h1 : 1 / (M : ℝ) - 1 / ((M : ℝ) + 1) = 1 / ((M : ℝ) * ((M : ℝ) + 1)) := by
        field_simp
        ring
      rw [h1, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
