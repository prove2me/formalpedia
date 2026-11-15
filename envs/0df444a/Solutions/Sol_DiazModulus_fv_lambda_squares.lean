-- Prove2me | solution 1 for DiazModulus.fv_lambda_squares
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:32:29.532797+00:00
-- url     : https://prove2.me/submissions/d4030228-17c6-475c-82a8-7e8e078acf27

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fv_theorem_1_2

open Complex ComplexConjugate

/-! # The `Λ²` corollary

Apply Theorem 1.2 to the matrix `M = (Λ₀ Λ₁ Λ₂; Λ₁ Λ₂ Λ₀)`, whose entries lie in `ℒ̃`. Its three
`2 × 2` minors are `Λ₁Λ₀ − Λ₂²`, `Λ₂Λ₁ − Λ₀²` and `Λ₀Λ₂ − Λ₁²`, the negatives of the three numbers in the
statement, and `ℒ̃` is closed under negation. Both freeness hypotheses follow from the freeness of
`1, Λ₀, Λ₁, Λ₂`. A relation among the rows of `(M; I₃)` has first coordinate `c₀ + aΛ₀ + bΛ₁ = 0`, so
`a = b = c₀ = 0`, and then the other two coordinates give `c₁ = c₂ = 0`. A relation among the columns of
`(I₂, M)` has first coordinate `a + c₀Λ₀ + c₁Λ₁ + c₂Λ₂ = 0`, so `a = c₀ = c₁ = c₂ = 0`, and then the
second coordinate gives `b = 0`. -/

namespace RC3_A8
open DiazModulus

theorem four_free (Λ : Fin 3 → ℂ) (hfree : LinearIndependent (↥Qbar) ![1, Λ 0, Λ 1, Λ 2])
    (a b c d : ↥Qbar) (h : (a : ℂ) + b * Λ 0 + c * Λ 1 + d * Λ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have := Fintype.linearIndependent_iff.mp hfree ![a, b, c, d] (by
    simp only [Fin.sum_univ_four, Subfield.smul_def]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, smul_eq_mul, mul_one]
    exact h)
  exact ⟨this 0, this 1, this 2, this 3⟩

end RC3_A8

open DiazModulus RC3_A8 in
theorem solution (Λ : Fin 3 → ℂ) (hΛ : ∀ i, Λ i ∈ LogAlgTilde)
    (hfree : LinearIndependent (↥Qbar) ![1, Λ 0, Λ 1, Λ 2]) :
    Λ 0 ^ 2 - Λ 1 * Λ 2 ∉ LogAlgTilde ∨ Λ 1 ^ 2 - Λ 2 * Λ 0 ∉ LogAlgTilde ∨
      Λ 2 ^ 2 - Λ 0 * Λ 1 ∉ LogAlgTilde := by
  set M : Matrix (Fin 2) (Fin 3) ℂ := !![Λ 0, Λ 1, Λ 2; Λ 1, Λ 2, Λ 0] with hMdef
  have hM : ∀ i j, M i j ∈ LogAlgTilde := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [hMdef, hΛ]
  have hrows : LinearIndependent (↥Qbar) (Matrix.fromRows M (1 : Matrix (Fin 3) (Fin 3) ℂ)).row := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have e0 := congrFun hg 0
    have e1 := congrFun hg 1
    have e2 := congrFun hg 2
    simp [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.row, hMdef,
      Subfield.smul_def] at e0 e1 e2
    obtain ⟨h0, h1, h2, -⟩ := four_free Λ hfree (g (Sum.inr 0)) (g (Sum.inl 0)) (g (Sum.inl 1)) 0
      (by push_cast; linear_combination e0)
    have h3 : g (Sum.inr 1) = 0 := by simpa [h1, h2] using e1
    have h4 : g (Sum.inr 2) = 0 := by simpa [h1, h2] using e2
    rintro (i | j)
    · fin_cases i
      exacts [h1, h2]
    · fin_cases j
      exacts [h0, h3, h4]
  have hcols : LinearIndependent (↥Qbar) (Matrix.fromCols (1 : Matrix (Fin 2) (Fin 2) ℂ) M).col := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have e0 := congrFun hg 0
    have e1 := congrFun hg 1
    simp [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.col, hMdef,
      Subfield.smul_def] at e0 e1
    obtain ⟨h0, h1, h2, h3⟩ := four_free Λ hfree (g (Sum.inl 0)) (g (Sum.inr 0)) (g (Sum.inr 1))
      (g (Sum.inr 2)) (by linear_combination e0)
    have h4 : g (Sum.inl 1) = 0 := by simpa [h1, h2, h3] using e1
    rintro (i | j)
    · fin_cases i
      exacts [h0, h4]
    · fin_cases j
      exacts [h1, h2, h3]
  have h := DiazModulus.fv_theorem_1_2 M hM hrows hcols
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c2, c3⟩ := hcon
  rcases h with h | h | h <;> apply h
  · convert neg_mem c3 using 1; simp [hMdef]; ring
  · convert neg_mem c1 using 1; simp [hMdef]; ring
  · convert neg_mem c2 using 1; simp [hMdef]; ring
