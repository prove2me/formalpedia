-- Prove2me | solution 1 for BlockCycleRotation.getLast_opt_drop_of_getLast_opt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:57:53.040033+00:00
-- url     : https://prove2.me/submissions/bbd52a30-b879-4e7d-b163-963afd08cb29

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
/-- A suffix inherits the last-entry condition. -/
theorem solution {L : List ℕ} {j : ℕ} (hj : j < L.length)
    (hlast : ∀ x ∈ L.getLast?, 2 ≤ x) : ∀ x ∈ (L.drop j).getLast?, 2 ≤ x:= by
  have hdropne : L.drop j ≠ [] := by
    intro hc
    have hl : (L.drop j).length = 0 := by rw [hc]; simp
    rw [List.length_drop] at hl
    omega
  have hgl : L.getLast? = (L.drop j).getLast? := by
    conv_lhs => rw [← List.take_append_drop j L]
    exact List.getLast?_append_of_ne_nil _ hdropne
  intro x hx
  exact hlast x (hgl ▸ hx)
