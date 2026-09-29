-- Prove2me | solution 1 for DiazModulus.generic_conj_pair_four_exp_barrier
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T20:42:25.217012+00:00
-- url     : https://prove2.me/submissions/c9cc1a9c-2db3-4cc1-b81a-94c3e35d01c0

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_generic_conj_pair_no_quadratic_relation
import Theorems.Thm_DiazModulus_det_zero_linear_forms_rank_one

open Complex ComplexConjugate

namespace GenConjFourExp

/-- A `ℚ`-linear relation between the coefficient vectors of two linear forms in `e` gives the
same relation between the forms. -/
theorem forms_rel (e : Fin 3 → ℂ) (a b : Fin 3 → ℚ) (p q : ℚ)
    (hab : ∀ k, p * a k + q * b k = 0) :
    (p : ℂ) * ∑ k, (a k : ℂ) * e k + (q : ℂ) * ∑ k, (b k : ℂ) * e k = 0 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  have hC : ((p * a k + q * b k : ℚ) : ℂ) = 0 := by exact_mod_cast hab k
  push_cast at hC
  linear_combination e k * hC

end GenConjFourExp

open GenConjFourExp in
theorem solution (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥DiazModulus.Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I])
    (A : Fin 2 → Fin 2 → Fin 3 → ℚ) (M : Fin 2 → Fin 2 → ℂ)
    (hM : ∀ i j, M i j = ∑ k, (A i j k : ℂ) * ![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k)
    (hdet : M 0 0 * M 1 1 = M 0 1 * M 1 0) :
    (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ j, (p : ℂ) * M 0 j + (q : ℂ) * M 1 j = 0) ∨
      (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ i, (p : ℂ) * M i 0 + (q : ℂ) * M i 1 = 0) := by
  set e : Fin 3 → ℂ := ![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] with he
  -- the quadratic form `M 0 0 * M 1 1 - M 0 1 * M 1 0`, written in the basis `e`
  let F : Fin 3 → Fin 3 → ℚ := fun k l => A 0 0 k * A 1 1 l - A 0 1 k * A 1 0 l
  have hF : ∑ k, ∑ l, (F k l : ℂ) * (e k * e l) = 0 := by
    have h1 : ∑ k, ∑ l, (F k l : ℂ) * (e k * e l) = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
      rw [hM 0 0, hM 1 1, hM 0 1, hM 1 0, Finset.sum_mul_sum, Finset.sum_mul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp only [F]
      push_cast
      ring
    rw [h1, hdet, sub_self]
  have hsym := DiazModulus.generic_conj_pair_no_quadratic_relation u hu hρ hgen F hF
  have hdet' : ∀ k l : Fin 3,
      A 0 0 k * A 1 1 l + A 0 0 l * A 1 1 k = A 0 1 k * A 1 0 l + A 0 1 l * A 1 0 k := by
    intro k l
    have := hsym k l
    simp only [F] at this
    linarith
  rcases DiazModulus.det_zero_linear_forms_rank_one 3 A hdet' with
    ⟨p, q, hpq, hrow⟩ | ⟨p, q, hpq, hcol⟩
  · left
    refine ⟨p, q, hpq, fun j => ?_⟩
    rw [hM 0 j, hM 1 j]
    exact forms_rel e (A 0 j) (A 1 j) p q (fun k => hrow j k)
  · right
    refine ⟨p, q, hpq, fun i => ?_⟩
    rw [hM i 0, hM i 1]
    exact forms_rel e (A i 0) (A i 1) p q (fun k => hcol i k)

#print axioms solution
