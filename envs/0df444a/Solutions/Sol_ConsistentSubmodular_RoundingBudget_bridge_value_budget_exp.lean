-- Prove2me | solution 1 for ConsistentSubmodular.RoundingBudget.bridge_value_budget_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:30:42.495831+00:00
-- url     : https://prove2.me/submissions/256e26f3-833d-465f-ba56-605bfef8c2d7

import Mathlib

section

namespace ConsistentSubmodular

namespace RoundingBudget

/-- `exp (-c) ≤ 1 / B` once `B ≤ 2 ^ c`. -/
theorem exp_neg_le_inv_of_le_two_pow {B c : ℕ} (hB : 0 < B) (hc : B ≤ 2 ^ c) :
    Real.exp (-(c : ℝ)) ≤ 1 / B := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ c ≤ Real.exp c := by
    calc (2 : ℝ) ^ c ≤ Real.exp 1 ^ c := pow_le_pow_left₀ (by norm_num) h2 c
      _ = Real.exp c := by rw [← Real.exp_nat_mul, mul_one]
  have hBr : (B : ℝ) ≤ Real.exp c := (by exact_mod_cast hc : (B : ℝ) ≤ 2 ^ c).trans hpow
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by exact_mod_cast hB) hBr

end RoundingBudget

end ConsistentSubmodular

end

section

open ConsistentSubmodular
open ConsistentSubmodular.RoundingBudget

theorem solution (B N c H : ℕ) (V : ℝ) (hB : 0 < B) (hN : 0 < N)
    (hV : 0 < V) (hH0 : 0 < H) (hc : 4 * B ≤ 2 ^ c) (hH : 8 * N ^ 2 * c ≤ H) :
    Real.exp (-((V / N) ^ 2) / (2 * (2 * V / H) * (2 * V))) ≤ 1 / (4 * B) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH0
  have hexp : -((V / N) ^ 2) / (2 * (2 * V / H) * (2 * V)) =
      -((H : ℝ) / (8 * (N : ℝ) ^ 2)) := by
    field_simp
    ring
  rw [hexp]
  have hge : (c : ℝ) ≤ (H : ℝ) / (8 * (N : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have := (by exact_mod_cast hH : ((8 * N ^ 2 * c : ℕ) : ℝ) ≤ H)
    push_cast at this
    linarith
  have h := exp_neg_le_inv_of_le_two_pow (B := 4 * B) (by positivity) hc
  push_cast at h
  exact (Real.exp_le_exp.mpr (neg_le_neg hge)).trans h

end
