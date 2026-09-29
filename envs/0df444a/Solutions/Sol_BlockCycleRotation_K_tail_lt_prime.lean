-- Prove2me | solution 1 for BlockCycleRotation.K_tail_lt_prime
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:51:25.917404+00:00
-- url     : https://prove2.me/submissions/76073071-1beb-4b40-b1b4-14caf41c0802

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_K_tail_lt
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
/-- `K l.tail < K l`, allowing a one-element list provided its entry is at least
`2` — Heilbronn's condition `2 ≤ c_l`. -/
theorem solution {l : List ℕ} (hne : l ≠ []) (hpos : ∀ c ∈ l, 1 ≤ c)
    (hsingle : l.length = 1 → 2 ≤ K l) : K l.tail < K l:= by
  rcases Nat.lt_or_ge l.length 2 with hlen | hlen
  · have h1 : l.length = 1 := by
      have hne' : l.length ≠ 0 := by simpa using hne
      omega
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.1 h1
    subst hc
    have h2 := hsingle h1
    simp at h2 ⊢
    omega
  · exact K_tail_lt l hlen hpos
