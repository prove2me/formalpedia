-- Prove2me | solution 1 for BlockCycleRotation.tsum_tail_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:37:28.912857+00:00
-- url     : https://prove2.me/submissions/dd0e0eb6-9cb5-468b-91b2-b8366fd2d3eb

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_sum_inv_sq_tail_le
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
/-- The tail of `∑ 1/m²` past `n`. -/
theorem solution {n : ℕ} (hn : 0 < n) :
    ∑' j : ℕ, 1 / ((n : ℝ) + (j : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ):= by
  refine Real.tsum_le_of_sum_le (fun j => by positivity) fun s => ?_
  have hcast : ∀ j : ℕ, 1 / ((n : ℝ) + (j : ℝ) + 1) ^ 2 = 1 / (((n + j + 1 : ℕ) : ℝ)) ^ 2 := by
    intro j; push_cast; ring
  simp only [hcast]
  have himg : ∑ x ∈ s.image (fun j => n + j + 1), 1 / ((x : ℝ)) ^ 2
      = ∑ x ∈ s, 1 / (((n + x + 1 : ℕ) : ℝ)) ^ 2 :=
    Finset.sum_image (by
      intro x _ y _ h
      have h' : n + x + 1 = n + y + 1 := h
      omega)
  rw [← himg]
  refine sum_inv_sq_tail_le hn _ ?_
  intro a ha
  simp only [Finset.mem_image] at ha
  obtain ⟨x, -, rfl⟩ := ha
  omega
