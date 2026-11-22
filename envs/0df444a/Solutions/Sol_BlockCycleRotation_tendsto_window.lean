-- Prove2me | solution 1 for BlockCycleRotation.tendsto_window
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-05T11:21:41.435284+00:00
-- url     : https://prove2.me/submissions/37112502-e29f-42f8-b65b-56d4e380108b

import Mathlib

open Real Finset Filter Topology

theorem solution (n : ℕ) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)) atTop (𝓝 0) := by
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
