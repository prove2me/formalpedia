-- Prove2me | solution 1 for BlockCycleRotation.tendsto_window
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:37:08.048657+00:00
-- url     : https://prove2.me/submissions/43b56fd8-9718-4f3b-be42-b4e72807d1a5

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset Filter Topology

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
/-- The moving window of `n` terms tends to zero. -/
theorem solution (n : ℕ) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)) atTop (𝓝 0):= by
  have hz : Tendsto (fun N : ℕ => (n : ℝ) * (1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
    have h : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h.const_mul (n : ℝ)
    rw [mul_zero] at h2
    exact h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
    (fun N => Finset.sum_nonneg fun j _ => by positivity) (fun N => ?_)
  calc ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)
      ≤ ∑ _j ∈ Finset.Ico N (N + n), 1 / ((N : ℝ) + 1) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.mem_Ico] at hj
        have : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
    _ = (n : ℝ) * (1 / ((N : ℝ) + 1)) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        simp
