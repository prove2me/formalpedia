-- Prove2me | solution 1 for DiazModulus.generic_quadratic_relation_is_norm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T04:58:31.326744+00:00
-- url     : https://prove2.me/submissions/0f4f491e-9ad8-4777-92c8-0c86055a2c91

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace P14Norm

open MvPolynomial

/-- The polynomial `c0 + c1 U + c2 U² + c3 U³ + c4 U⁴ + c5 U W + c6 U² W + c7 U³ W + c8 U² W²`
over `Q̄`, in the variables `U = X 0` and `W = X 1`. -/
noncomputable def Q (c0 c1 c2 c3 c4 c5 c6 c7 c8 : ↥DiazModulus.Qbar) :
    MvPolynomial (Fin 2) ↥DiazModulus.Qbar :=
  C c0 + C c1 * X 0 + C c2 * X 0 ^ 2 + C c3 * X 0 ^ 3 + C c4 * X 0 ^ 4
    + C c5 * X 0 * X 1 + C c6 * X 0 ^ 2 * X 1 + C c7 * X 0 ^ 3 * X 1 + C c8 * X 0 ^ 2 * X 1 ^ 2

theorem aeval_Q (c0 c1 c2 c3 c4 c5 c6 c7 c8 : ↥DiazModulus.Qbar) (a b : ℂ) :
    aeval ![a, b] (Q c0 c1 c2 c3 c4 c5 c6 c7 c8) =
      (c0 : ℂ) + (c1 : ℂ) * a + (c2 : ℂ) * a ^ 2 + (c3 : ℂ) * a ^ 3 + (c4 : ℂ) * a ^ 4
        + (c5 : ℂ) * a * b + (c6 : ℂ) * a ^ 2 * b + (c7 : ℂ) * a ^ 3 * b
        + (c8 : ℂ) * a ^ 2 * b ^ 2 := by
  simp [Q]
  rfl

/-- A polynomial function `ℂ² → ℂ` supported on the nine monomials
`1, U, U², U³, U⁴, U W, U² W, U³ W, U² W²` that vanishes identically has zero coefficients:
read them off from the values at eleven integer points. -/
theorem coeffs_eq_zero (c0 c1 c2 c3 c4 c5 c6 c7 c8 : ℂ)
    (h : ∀ a b : ℂ, c0 + c1 * a + c2 * a ^ 2 + c3 * a ^ 3 + c4 * a ^ 4 + c5 * a * b
      + c6 * a ^ 2 * b + c7 * a ^ 3 * b + c8 * a ^ 2 * b ^ 2 = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 ∧ c7 = 0 ∧ c8 = 0 := by
  have e00 := h 0 0
  have e10 := h 1 0
  have em0 := h (-1) 0
  have e20 := h 2 0
  have em20 := h (-2) 0
  have e11 := h 1 1
  have e1m := h 1 (-1)
  have em11 := h (-1) 1
  have em1m := h (-1) (-1)
  have e21 := h 2 1
  have e2m := h 2 (-1)
  have h0 : c0 = 0 := by linear_combination e00
  have h8 : c8 = 0 := by linear_combination (1 / 2 : ℂ) * e11 + (1 / 2 : ℂ) * e1m - e10
  have h6 : c6 = 0 := by
    linear_combination (1 / 4 : ℂ) * e11 - (1 / 4 : ℂ) * e1m + (1 / 4 : ℂ) * em11
      - (1 / 4 : ℂ) * em1m
  have h7 : c7 = 0 := by
    linear_combination (1 / 12 : ℂ) * e21 - (1 / 12 : ℂ) * e2m - (2 / 3 : ℂ) * h6
      - (1 / 12 : ℂ) * e11 + (1 / 12 : ℂ) * e1m + (1 / 12 : ℂ) * em11 - (1 / 12 : ℂ) * em1m
  have h5 : c5 = 0 := by
    linear_combination (1 / 4 : ℂ) * e11 - (1 / 4 : ℂ) * e1m - (1 / 4 : ℂ) * em11
      + (1 / 4 : ℂ) * em1m - h7
  have h4 : c4 = 0 := by
    linear_combination (1 / 24 : ℂ) * e20 + (1 / 24 : ℂ) * em20 - (1 / 6 : ℂ) * e10
      - (1 / 6 : ℂ) * em0 + (1 / 4 : ℂ) * h0
  have h2 : c2 = 0 := by
    linear_combination (1 / 2 : ℂ) * e10 + (1 / 2 : ℂ) * em0 - h0 - h4
  have h3 : c3 = 0 := by
    linear_combination (1 / 12 : ℂ) * e20 - (1 / 12 : ℂ) * em20 - (1 / 6 : ℂ) * e10
      + (1 / 6 : ℂ) * em0
  have h1 : c1 = 0 := by
    linear_combination (1 / 2 : ℂ) * e10 - (1 / 2 : ℂ) * em0 - h3
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩

end P14Norm

open P14Norm in
/-- Write `w = πi`, `ρ = u ū` and `S_kl = P k l + P l k`. Since `ū = ρ / u`, multiplying the
relation by `u²` gives a polynomial identity in `(u, w)` with coefficients in `Q̄`:
`ρ² P₂₂ + ρ S₀₂ u + (P₀₀ + ρ S₁₂) u² + S₀₁ u³ + P₁₁ u⁴ + ρ S₂₃ u w + S₀₃ u² w + S₁₃ u³ w
+ P₃₃ u² w² = 0`. By algebraic independence every coefficient vanishes, so the quadratic form
reduces to `P₀₀ x₀² + S₁₂ x₁ x₂ = S₁₂ (x₁ x₂ - ρ x₀²)`. -/
theorem solution (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥DiazModulus.Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I])
    (P : Fin 4 → Fin 4 → ℂ) (hP : ∀ k l, IsAlgebraic ℚ (P k l))
    (hrel : ∑ k, ∑ l, P k l * ![1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k
      * ![1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] l = 0) :
    ∃ c : ℂ, IsAlgebraic ℚ c ∧
      ∀ x : Fin 4 → ℂ, ∑ k, ∑ l, P k l * x k * x l = c * (x 1 * x 2 - u * conj u * x 0 ^ 2) := by
  have hρQ : u * conj u ∈ DiazModulus.Qbar := DiazModulus.mem_Qbar_iff.2 hρ
  have hρ0 : u * conj u ≠ 0 := mul_ne_zero hu ((map_ne_zero _).2 hu)
  set w : ℂ := ((Real.pi : ℝ) : ℂ) * Complex.I with hw
  let r : ↥DiazModulus.Qbar := ⟨u * conj u, hρQ⟩
  let q : Fin 4 → Fin 4 → ↥DiazModulus.Qbar := fun k l => ⟨P k l, DiazModulus.mem_Qbar_iff.2 (hP k l)⟩
  let Pu : MvPolynomial (Fin 2) ↥DiazModulus.Qbar :=
    Q (r ^ 2 * q 2 2) (r * (q 0 2 + q 2 0)) (q 0 0 + r * (q 1 2 + q 2 1)) (q 0 1 + q 1 0)
      (q 1 1) (r * (q 2 3 + q 3 2)) (q 0 3 + q 3 0) (q 1 3 + q 3 1) (q 3 3)
  have hval : ∀ a b : ℂ, MvPolynomial.aeval ![a, b] Pu =
      (u * conj u) ^ 2 * P 2 2 + u * conj u * (P 0 2 + P 2 0) * a
        + (P 0 0 + u * conj u * (P 1 2 + P 2 1)) * a ^ 2 + (P 0 1 + P 1 0) * a ^ 3
        + P 1 1 * a ^ 4 + u * conj u * (P 2 3 + P 3 2) * a * b + (P 0 3 + P 3 0) * a ^ 2 * b
        + (P 1 3 + P 3 1) * a ^ 3 * b + P 3 3 * a ^ 2 * b ^ 2 := by
    intro a b
    simp only [Pu, aeval_Q]
    push_cast
    rfl
  have h0 : MvPolynomial.aeval ![u, w] Pu = 0 := by
    rw [hval]
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hrel
    linear_combination u ^ 2 * hrel
  have hPu : Pu = 0 := hgen.eq_zero_of_aeval_eq_zero Pu h0
  have ev : ∀ a b : ℂ, (u * conj u) ^ 2 * P 2 2 + u * conj u * (P 0 2 + P 2 0) * a
        + (P 0 0 + u * conj u * (P 1 2 + P 2 1)) * a ^ 2 + (P 0 1 + P 1 0) * a ^ 3
        + P 1 1 * a ^ 4 + u * conj u * (P 2 3 + P 3 2) * a * b + (P 0 3 + P 3 0) * a ^ 2 * b
        + (P 1 3 + P 3 1) * a ^ 3 * b + P 3 3 * a ^ 2 * b ^ 2 = 0 := by
    intro a b
    rw [← hval, hPu, map_zero]
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := coeffs_eq_zero _ _ _ _ _ _ _ _ _ ev
  have hP22 : P 2 2 = 0 :=
    (mul_eq_zero.1 c0).resolve_left (pow_ne_zero 2 hρ0)
  have hS02 : P 0 2 + P 2 0 = 0 := (mul_eq_zero.1 c1).resolve_left hρ0
  have hS23 : P 2 3 + P 3 2 = 0 := (mul_eq_zero.1 c5).resolve_left hρ0
  refine ⟨P 1 2 + P 2 1, ?_, ?_⟩
  · exact DiazModulus.mem_Qbar_iff.1
      (add_mem (DiazModulus.mem_Qbar_iff.2 (hP 1 2)) (DiazModulus.mem_Qbar_iff.2 (hP 2 1)))
  · intro x
    simp only [Fin.sum_univ_four]
    linear_combination x 0 ^ 2 * c2 + x 1 ^ 2 * c4 + x 2 ^ 2 * hP22 + x 3 ^ 2 * c8
      + x 0 * x 1 * c3 + x 0 * x 2 * hS02 + x 0 * x 3 * c6 + x 1 * x 3 * c7 + x 2 * x 3 * hS23

#print axioms solution
