-- Prove2me | solution 1 for BlockCycleRotation.heilbronn_surjective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:54:09.018289+00:00
-- url     : https://prove2.me/submissions/be55ed51-76a8-4053-a23e-040df2176a6d

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_K_append
import Theorems.Thm_BlockCycleRotation_K_reverse
import Theorems.Thm_BlockCycleRotation_K_cf
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

/-- Mirror of the earlier reversal identity. -/
theorem reverse_tail_eq (l : List ℕ) : (l.reverse).tail = (l.dropLast).reverse := by
  have h : ((l.reverse).reverse).dropLast = ((l.reverse).tail).reverse := by
    rcases hl : l.reverse with _ | ⟨a, t⟩ <;> simp
  rw [List.reverse_reverse] at h
  rw [h, List.reverse_reverse]

end BlockCycleRotation

open BlockCycleRotation in
/-- **Heilbronn's correspondence, surjectivity at the level of quadruples.**

Every quadruple `(a, b, a', b')` with `a > a' ≥ 1`, `b > b' ≥ 1` and both
coprimality conditions arises from a split expansion, and its continuant
identity `n = a·b + a'·b'` holds.  The suffix is obtained by reversing, which is
legitimate by `K_reverse`. -/
theorem solution {a b a' b' : ℕ}
    (ha : 1 ≤ a') (hab : a' < a) (hga : Nat.gcd a a' = 1)
    (hb : 1 ≤ b') (hbb : b' < b) (hgb : Nat.gcd b b' = 1) :
    ∃ l₁ l₂ : List ℕ, l₁ ≠ [] ∧ l₂ ≠ [] ∧
      K l₁ = a ∧ K l₁.dropLast = a' ∧ K l₂ = b ∧ K l₂.tail = b' ∧
      K (l₁ ++ l₂) = a * b + a' * b':= by
  obtain ⟨hK₁, hKd₁⟩ := K_cf a' a ha hab hga
  obtain ⟨hne₁, -, -⟩ := cf_spec a' a ha hab hga
  obtain ⟨hK₂, hKd₂⟩ := K_cf b' b hb hbb hgb
  obtain ⟨hne₂, -, -⟩ := cf_spec b' b hb hbb hgb
  have hne₂' : (cf b b').reverse ≠ [] := by simpa using hne₂
  have hb₂ : K (cf b b').reverse = b := by rw [K_reverse]; exact hK₂
  have hb₂' : K ((cf b b').reverse).tail = b' := by
    rw [reverse_tail_eq, K_reverse]; exact hKd₂
  refine ⟨cf a a', (cf b b').reverse, hne₁, hne₂', hK₁, hKd₁, hb₂, hb₂', ?_⟩
  rw [K_append _ _ hne₁ hne₂', hK₁, hKd₁, hb₂, hb₂']
