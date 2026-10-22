-- Prove2me | solution 1 for GDGen3.pow_slope_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:18:54.519966+00:00
-- url     : https://prove2.me/submissions/86d29883-107e-4edd-949b-f56e575b88be

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (z : ℝ) (hz : 1 < z) :
    StrictMono (fun n : ℕ => (z ^ (n + 1) - 1) / ((n : ℝ) + 1)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hsum : (∑ k ∈ range (n + 1), z ^ k) < ((n : ℝ) + 1) * z ^ (n + 1) := by
    calc
      _ < ∑ k ∈ range (n + 1), z ^ (n + 1) := by
        apply sum_lt_sum
        · intro k hk; exact le_of_lt (pow_lt_pow_right₀ hz (mem_range.mp hk))
        · exact ⟨0, by simp, pow_lt_pow_right₀ hz (by omega)⟩
      _ = _ := by simp
  have hm := mul_lt_mul_of_pos_right hsum (by linarith : 0 < z - 1)
  rw [geom_sum_mul] at hm
  apply (div_lt_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)
    (by positivity : 0 < ((n + 1 : ℕ) : ℝ) + 1)).2
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  rw [pow_succ] at hm
  nlinarith
