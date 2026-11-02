-- Prove2me | solution 1 for DiazModulus.five_exponentials
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T09:23:51.392773+00:00
-- url     : https://prove2.me/submissions/720fb88b-2d90-4a42-8318-7e506747654d

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_Schanuel_baker_linear_forms_in_logarithms
import Theorems.Thm_DiazModulus_strong_six_exponentials_unconditional

open Complex ComplexConjugate

/-! # The five exponentials theorem

Waldschmidt 1988, Cor. 2.2, p. 378; DALAG § 11.3.3, Example 1, p. 385. The route is DALAG's Remark after
Cor. 11.16, p. 399: Roy's strong six exponentials theorem plus Baker's theorem.

Suppose the five exponentials are algebraic. Put `y₃ = η / x₁` (indices from `1` as in the sources).
* Each `xᵢ y₁` is a logarithm of an algebraic number, and the `xᵢ y₁` are `ℚ`-independent (multiply `x` by
  `y₁ ≠ 0`). Baker's theorem with `b₀ = 0` turns a `Q̄`-relation `Σ gᵢ xᵢ = 0` into the relation
  `Σ gᵢ (xᵢ y₁) = 0`, which forces `g = 0`. So `x` is `Q̄`-independent.
* A `Q̄`-relation `g₁ y₁ + g₂ y₂ + g₃ y₃ = 0`, multiplied by `x₁`, reads `g₃ η + g₁ (x₁ y₁) + g₂ (x₁ y₂) = 0`.
  Baker's theorem with the constant term `b₀ = g₃ η` forces `g = 0`, since `η ≠ 0`.
* The six products lie in `ℒ̃`: four are logarithms by hypothesis, `x₁ y₃ = η ∈ Q̄` and
  `x₂ y₃ = η x₂ / x₁` is a logarithm by hypothesis.

Roy's theorem `strong_six_exponentials_unconditional` then gives the contradiction. -/

open DiazModulus in
theorem solution :
    ∀ x y : Fin 2 → ℂ, ∀ η : ℂ, LinearIndependent ℚ x → LinearIndependent ℚ y →
      IsAlgebraic ℚ η → η ≠ 0 →
      ¬ ((∀ i j, IsAlgebraic ℚ (Complex.exp (x i * y j))) ∧
          IsAlgebraic ℚ (Complex.exp (η * x 1 / x 0))) := by
  intro x y η hx hy hη hη0 ⟨h, hη'⟩
  have hx0 : x 0 ≠ 0 := hx.ne_zero 0
  have hy0 : y 0 ≠ 0 := hy.ne_zero 0
  have logmem : ∀ u : ℂ, IsAlgebraic ℚ (Complex.exp u) → u ∈ LogAlgTilde := fun u hu =>
    Submodule.subset_span (Set.mem_insert_of_mem _ hu)
  have algmem : ∀ a : ℂ, IsAlgebraic ℚ a → a ∈ LogAlgTilde := fun a ha => by
    have := Submodule.smul_mem LogAlgTilde (⟨a, mem_Qbar_iff.mpr ha⟩ : Qbar)
      (Submodule.subset_span (Set.mem_insert 1 LogAlg) : (1 : ℂ) ∈ LogAlgTilde)
    simpa [Subfield.smul_def] using this
  -- `x` is `Q̄`-independent.
  have hxQ : LinearIndependent Qbar x := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hne
    push Not at hne
    obtain ⟨i, hi⟩ := hne
    apply Schanuel.baker_linear_forms_in_logarithms 2 (fun i => x i * y 0)
      (hx.map' (LinearMap.mulRight ℚ (y 0)) (LinearMap.ker_eq_bot.mpr (mul_left_injective₀ hy0)))
      (fun i => h i 0) 0 (fun i => (g i : ℂ)) isAlgebraic_zero (fun i => mem_Qbar_iff.mp (g i).2)
      (Or.inr ⟨i, by exact_mod_cast hi⟩)
    have e : ∑ i, (g i : ℂ) * (x i * y 0) = (∑ i, g i • x i) * y 0 := by
      simp [Subfield.smul_def]; ring
    rw [zero_add, e, hg, zero_mul]
  -- `y' = (y₁, y₂, η / x₁)` is `Q̄`-independent.
  have hyQ : LinearIndependent Qbar ![y 0, y 1, η / x 0] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Subfield.smul_def] at hg
    by_contra hne
    push Not at hne
    obtain ⟨i, hi⟩ := hne
    have hi' : (g i : ℂ) ≠ 0 := by exact_mod_cast hi
    apply Schanuel.baker_linear_forms_in_logarithms 2 (fun j => x 0 * y j)
      (hy.map' (LinearMap.mulLeft ℚ (x 0)) (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ hx0)))
      (fun j => h 0 j) ((g 2 : ℂ) * η) ![(g 0 : ℂ), (g 1 : ℂ)]
      (mem_Qbar_iff.mp (mul_mem (g 2).2 (mem_Qbar_iff.mpr hη)))
      (fun j => by fin_cases j <;> exact mem_Qbar_iff.mp (g _).2)
      (by fin_cases i
          · exact Or.inr ⟨0, hi'⟩
          · exact Or.inr ⟨1, hi'⟩
          · exact Or.inl (mul_ne_zero hi' hη0))
    have e' : x 0 * (η / x 0) = η := mul_div_cancel₀ η hx0
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (x 0) * hg - (g 2 : ℂ) * e'
  refine strong_six_exponentials_unconditional x ![y 0, y 1, η / x 0] hxQ hyQ ?_
  intro i j
  fin_cases j
  · exact logmem _ (h i 0)
  · exact logmem _ (h i 1)
  · fin_cases i
    · simpa [mul_div_cancel₀ η hx0] using algmem η hη
    · show x 1 * (η / x 0) ∈ LogAlgTilde
      rw [show x 1 * (η / x 0) = η * x 1 / x 0 by ring]
      exact logmem _ hη'
