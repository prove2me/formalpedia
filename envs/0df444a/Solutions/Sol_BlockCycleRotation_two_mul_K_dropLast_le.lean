-- Prove2me | solution 1 for BlockCycleRotation.two_mul_K_dropLast_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:54:49.736753+00:00
-- url     : https://prove2.me/submissions/c4e4decc-54c6-4a2d-aa6b-92a491495df8

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_K_append
import Theorems.Thm_BlockCycleRotation_K_pos
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

/-- The mirrored recursion: appending an entry at the end. -/
theorem K_concat (l : List ℕ) (h : l ≠ []) (c : ℕ) :
    K (l ++ [c]) = c * K l + K l.dropLast := by
  rw [K_append l [c] h (by simp)]
  simp [Nat.mul_comm]

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- Conversely, an expansion whose last entry is at least `2` has
`2 · K L.dropLast ≤ K L`. -/
theorem solution : ∀ L : List ℕ, L ≠ [] → (∀ c ∈ L, 1 ≤ c) →
    (∀ x ∈ L.getLast?, 2 ≤ x) → 2 * K L.dropLast ≤ K L:= by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton m c _ =>
    intro _ hpos hlast
    have hc2 : 2 ≤ c := by
      apply hlast c
      simp
    have hdl : (m ++ [c]).dropLast = m := by simp
    rw [hdl]
    by_cases hm : m = []
    · subst hm
      simp
      omega
    · have hmp : 1 ≤ K m := K_pos m (fun x hx => hpos x (List.mem_append.2 (Or.inl hx)))
      rw [K_concat m hm c]
      nlinarith [Nat.zero_le (K m.dropLast)]
