-- Prove2me | solution 1 for BlockCycleRotation.K_tail_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:48:43.729539+00:00
-- url     : https://prove2.me/submissions/f869f32c-b458-4c48-b5cb-f5b93f368faa

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_K_reverse
import Theorems.Thm_BlockCycleRotation_K_dropLast_lt
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
/-- Dropping the first entry strictly decreases the continuant.  This is the
mirror image of `K_dropLast_lt`, via `K_reverse`. -/
theorem solution (l : List ℕ) (hlen : 2 ≤ l.length) (hpos : ∀ c ∈ l, 1 ≤ c) :
    K l.tail < K l:= by
  have hrev : (l.reverse).dropLast = (l.tail).reverse := by
    rcases l with _ | ⟨a, t⟩
    · simp
    · simp
  have hlen' : 2 ≤ l.reverse.length := by simpa using hlen
  have hpos' : ∀ c ∈ l.reverse, 1 ≤ c := by
    intro c hc
    exact hpos c (List.mem_reverse.1 hc)
  have h := K_dropLast_lt l.reverse hlen' hpos'
  rwa [hrev, K_reverse, K_reverse] at h
