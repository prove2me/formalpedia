-- Prove2me | solution 1 for BlockCycleRotation.heilbronn_bijection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:53:09.443909+00:00
-- url     : https://prove2.me/submissions/d2414622-6ef0-40da-8d2f-61e14ed64b47

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_K_cf
import Theorems.Thm_BlockCycleRotation_cf_K
import Theorems.Thm_BlockCycleRotation_cf_spec
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
/-- **Heilbronn's bijection.**

The map `l ↦ (K l, K l.dropLast)` is a bijection from normalised expansions
(nonempty, positive entries, first entry at least `2`) onto the coprime pairs
`a > a' ≥ 1`.  The first component is injectivity, the second surjectivity
together with the fact that the inverse lands among normalised expansions.

Combined with `heilbronn_forward`, this is the correspondence underlying
equation (eq. heilbron) of Blomer--Bux. -/
theorem solution :
    (∀ l : List ℕ, l ≠ [] → (∀ c ∈ l, 1 ≤ c) → (∀ x ∈ l.head?, 2 ≤ x) →
        cf (K l) (K l.dropLast) = l)
      ∧ (∀ a a' : ℕ, 1 ≤ a' → a' < a → Nat.gcd a a' = 1 →
        (cf a a' ≠ [] ∧ (∀ c ∈ cf a a', 1 ≤ c) ∧ (∀ x ∈ (cf a a').head?, 2 ≤ x))
          ∧ K (cf a a') = a ∧ K (cf a a').dropLast = a'):=
  ⟨cf_K, fun a a' h1 h2 h3 => ⟨cf_spec a' a h1 h2 h3, K_cf a' a h1 h2 h3⟩⟩
