-- Prove2me | solution 1 for DiazModulus.qbar_dependent_of_det_linear_forms
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:16:20.048773+00:00
-- url     : https://prove2.me/submissions/8409a01b-c13c-4d4e-a1c4-5a8e6fe3abad

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_det_zero_linear_forms_rank_one_field

namespace S7W1_qbar_dependent_of_det_linear_forms

/-- Polarisation of a vanishing difference of products of linear forms. -/
theorem polar2 (a b c d : Fin 4 → ℂ)
    (h : ∀ z : Fin 4 → ℂ,
      (∑ k, a k * z k) * (∑ k, b k * z k) - (∑ k, c k * z k) * (∑ k, d k * z k) = 0)
    (k l : Fin 4) : a k * b l + a l * b k = c k * d l + c l * d k := by
  have h1 := h (Pi.single k 1 + Pi.single l 1)
  have h2 := h (Pi.single k 1)
  have h3 := h (Pi.single l 1)
  simp [Pi.single_apply, mul_add, Finset.sum_add_distrib] at h1 h2 h3
  linear_combination h1 - h2 - h3

end S7W1_qbar_dependent_of_det_linear_forms

/- A `2 × 2` block of products `x i * y j` whose determinant vanishes identically as a quadratic
form: by `det_zero_linear_forms_rank_one_field` over `Q̄`, the rows or the columns satisfy an
algebraic linear relation. -/
open S7W1_qbar_dependent_of_det_linear_forms DiazModulus in
theorem solution {m : ℕ} (e : Fin 4 → ℂ) (C : Fin 2 → Fin m → Fin 4 → ℂ)
    (hC : ∀ i j k, IsAlgebraic ℚ (C i j k)) (x : Fin 2 → ℂ) (y : Fin m → ℂ) (j0 j1 : Fin m)
    (hx0 : x 0 ≠ 0) (hy0 : y j0 ≠ 0)
    (hxy : ∀ i j, x i * y j = ∑ k, C i j k * e k)
    (hdet : ∀ z : Fin 4 → ℂ, (∑ k, C 0 j0 k * z k) * (∑ k, C 1 j1 k * z k)
      - (∑ k, C 0 j1 k * z k) * (∑ k, C 1 j0 k * z k) = 0) :
    (∃ p q : ↥Qbar, ¬(p = 0 ∧ q = 0) ∧ (p : ℂ) * x 0 + (q : ℂ) * x 1 = 0) ∨
      (∃ p q : ↥Qbar, ¬(p = 0 ∧ q = 0) ∧ (p : ℂ) * y j0 + (q : ℂ) * y j1 = 0) := by
  have hpol := polar2 (C 0 j0) (C 1 j1) (C 0 j1) (C 1 j0) hdet
  let A : Fin 2 → Fin 2 → Fin 4 → ↥DiazModulus.Qbar :=
    fun i j k => ⟨C i (![j0, j1] j) k, DiazModulus.mem_Qbar_iff.2 (hC _ _ _)⟩
  have hA : ∀ i j k, ((A i j k : ↥DiazModulus.Qbar) : ℂ) = C i (![j0, j1] j) k :=
    fun _ _ _ => rfl
  have hdetA : ∀ k l : Fin 4,
      A 0 0 k * A 1 1 l + A 0 0 l * A 1 1 k = A 0 1 k * A 1 0 l + A 0 1 l * A 1 0 k := by
    intro k l
    apply Subtype.ext
    simp only [Subfield.coe_add, Subfield.coe_mul, hA, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hpol k l
  rcases DiazModulus.det_zero_linear_forms_rank_one_field 4 A hdetA with
    ⟨p, q, hpq, hr⟩ | ⟨p, q, hpq, hr⟩
  · left
    refine ⟨p, q, hpq, ?_⟩
    have hr' : ∀ k, (p : ℂ) * C 0 j0 k + (q : ℂ) * C 1 j0 k = 0 := by
      intro k
      have := congrArg Subtype.val (hr 0 k)
      simpa [hA] using this
    have e1 := hxy 0 j0
    have e2 := hxy 1 j0
    simp only [Fin.sum_univ_four] at e1 e2
    have h : ((p : ℂ) * x 0 + (q : ℂ) * x 1) * y j0 = 0 := by
      linear_combination (p : ℂ) * e1 + (q : ℂ) * e2 + e 0 * hr' 0 + e 1 * hr' 1
        + e 2 * hr' 2 + e 3 * hr' 3
    exact (mul_eq_zero.1 h).resolve_right hy0
  · right
    refine ⟨p, q, hpq, ?_⟩
    have hr' : ∀ k, (p : ℂ) * C 0 j0 k + (q : ℂ) * C 0 j1 k = 0 := by
      intro k
      have := congrArg Subtype.val (hr 0 k)
      simpa [hA] using this
    have e1 := hxy 0 j0
    have e2 := hxy 0 j1
    simp only [Fin.sum_univ_four] at e1 e2
    have h : x 0 * ((p : ℂ) * y j0 + (q : ℂ) * y j1) = 0 := by
      linear_combination (p : ℂ) * e1 + (q : ℂ) * e2 + e 0 * hr' 0 + e 1 * hr' 1
        + e 2 * hr' 2 + e 3 * hr' 3
    exact (mul_eq_zero.1 h).resolve_left hx0

#print axioms solution
