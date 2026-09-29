-- Prove2me | solution 1 for BlockCycleRotation.sum_inv_sq_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:28:36.925786+00:00
-- url     : https://prove2.me/submissions/087efc99-74fc-41d8-a9fe-13fc57a2c10d

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_sum_inv_sq_Ioc_le
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
/-- For any finite set of integers beyond `N`, the sum of `1/a²` is at most `1/N`. -/
theorem solution {N : ℕ} (hN : 0 < N) (s : Finset ℕ) (hs : ∀ a ∈ s, N < a) :
    ∑ a ∈ s, 1 / ((a : ℝ) ^ 2) ≤ 1 / (N : ℝ):= by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hM : N ≤ s.max' hne := le_of_lt (hs _ (s.max'_mem hne))
    have hsub : s ⊆ Finset.Ioc N (s.max' hne) := by
      intro a ha
      simp only [Finset.mem_Ioc]
      exact ⟨hs a ha, Finset.le_max' s a ha⟩
    calc ∑ a ∈ s, 1 / ((a : ℝ) ^ 2)
        ≤ ∑ a ∈ Finset.Ioc N (s.max' hne), 1 / ((a : ℝ) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 1 / (N : ℝ) - 1 / ((s.max' hne : ℕ) : ℝ) := sum_inv_sq_Ioc_le hN _ hM
      _ ≤ 1 / (N : ℝ) := by
          have : (0 : ℝ) ≤ 1 / ((s.max' hne : ℕ) : ℝ) := by positivity
          linarith
