-- Prove2me | solution 1 for DiazModulus.four_exp_barrier_of_no_quadratic_relation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:35:16.673183+00:00
-- url     : https://prove2.me/submissions/32650aad-c768-4418-a96c-9280a33bae6e

import Mathlib
import Theorems.Thm_DiazModulus_det_zero_linear_forms_rank_one

/- `det M = Σ_{k,l} (A₀₀ₖ A₁₁ₗ − A₀₁ₖ A₁₀ₗ) eₖ eₗ` is a rational quadratic relation among the `e k`,
so its coefficient matrix is alternating by `hnq`. That is the hypothesis of
`det_zero_linear_forms_rank_one`, whose rational row (column) relation among the coefficient vectors
gives the same relation among the rows (columns) of `M`. -/
theorem solution {n : ℕ} (e : Fin n → ℂ)
    (hnq : ∀ F : Fin n → Fin n → ℚ, ∑ k, ∑ l, (F k l : ℂ) * (e k * e l) = 0 →
      ∀ k l, F k l + F l k = 0)
    (A : Fin 2 → Fin 2 → Fin n → ℚ) (M : Fin 2 → Fin 2 → ℂ)
    (hM : ∀ i j, M i j = ∑ k, (A i j k : ℂ) * e k)
    (hdet : M 0 0 * M 1 1 = M 0 1 * M 1 0) :
    (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ j, (p : ℂ) * M 0 j + (q : ℂ) * M 1 j = 0) ∨
      (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ i, (p : ℂ) * M i 0 + (q : ℂ) * M i 1 = 0) := by
  have hexp : M 0 0 * M 1 1 - M 0 1 * M 1 0 =
      ∑ k, ∑ l, ((A 0 0 k * A 1 1 l - A 0 1 k * A 1 0 l : ℚ) : ℂ) * (e k * e l) := by
    simp only [hM, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    push_cast
    ring
  have hF := hnq (fun k l => A 0 0 k * A 1 1 l - A 0 1 k * A 1 0 l)
    (by rw [← hexp, hdet, sub_self])
  -- a rational relation among coefficient vectors becomes one among the entries of `M`
  have transfer : ∀ (p q : ℚ) (a b : Fin n → ℚ), (∀ k, p * a k + q * b k = 0) →
      (p : ℂ) * ∑ k, (a k : ℂ) * e k + (q : ℂ) * ∑ k, (b k : ℂ) * e k = 0 := by
    intro p q a b hab
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk : ((p * a k + q * b k : ℚ) : ℂ) = 0 := by exact_mod_cast hab k
    push_cast at hk
    linear_combination e k * hk
  rcases DiazModulus.det_zero_linear_forms_rank_one n A
      (fun k l => by linarith [hF k l]) with ⟨p, q, hpq, h⟩ | ⟨p, q, hpq, h⟩
  · exact Or.inl ⟨p, q, hpq, fun j => by rw [hM, hM]; exact transfer p q _ _ (h j)⟩
  · exact Or.inr ⟨p, q, hpq, fun i => by rw [hM, hM]; exact transfer p q _ _ (h i)⟩

#print axioms solution
