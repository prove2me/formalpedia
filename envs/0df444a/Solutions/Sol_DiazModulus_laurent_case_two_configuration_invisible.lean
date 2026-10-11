-- Prove2me | solution 1 for DiazModulus.laurent_case_two_configuration_invisible
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:24:53.076884+00:00
-- url     : https://prove2.me/submissions/a914b5a7-33cb-4489-8fbb-a6b95574a612

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The Laurent case `n = 2`: a configuration invisible to four-dimensional extensions

Let `u ∉ Q̄`. Then `u` is transcendental over `Q̄` (it is transcendental over `ℚ`, and `Q̄` is
algebraic over `ℚ`), so no non-zero polynomial over `Q̄` vanishes at `u` (`aeval_eq_zero`).
Take `x = (1, u)` and `y = (u⁻¹, 1, u³)`. A relation among `1, u`, or among `u⁻¹, 1, u³`
(multiplied by `u`), is a polynomial relation with distinct monomials, so both are free.
The six products are `u⁻¹, 1, u³, 1, u, u⁴`, so their span is `Q̄u⁻¹ + Q̄ + Q̄u + Q̄u³ + Q̄u⁴`
(both inclusions, element by element). Finally `u²`, `u⁻²` and `(u − b)⁻¹` (`b ∈ Q̄ \ {0}`)
are not in that span: write a membership as `t = c₁u⁻¹ + c₂ + c₃u + c₄u³ + c₅u⁴` and clear
denominators. For `u²` the coefficient of `X³` of the resulting zero polynomial is `-1`; for
`u⁻²` its constant coefficient is `1`; for `(u − b)⁻¹` the identity
`u = (u − b)(c₁ + c₂u + c₃u² + c₄u⁴ + c₅u⁵)` gives a zero polynomial whose value at `b` is `b ≠ 0`.
-/

namespace R9_laurentTwo

open DiazModulus Polynomial

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem algebraMap_coe (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem ne_zero_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : u ≠ 0 :=
  fun h => hu (h ▸ Subfield.zero_mem _)

/-- A member of the span of five elements is a `Q̄`-combination of them. -/
theorem mem_span5 {v a b c d e : ℂ}
    (h : v ∈ Submodule.span Qbar ({a, b, c, d, e} : Set ℂ)) :
    ∃ c₁ c₂ c₃ c₄ c₅ : ↥Qbar,
      v = (c₁ : ℂ) * a + c₂ * b + c₃ * c + c₄ * d + c₅ * e := by
  simp only [Submodule.mem_span_insert, Submodule.mem_span_singleton] at h
  obtain ⟨c₁, _, ⟨c₂, _, ⟨c₃, _, ⟨c₄, _, ⟨c₅, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
  exact ⟨c₁, c₂, c₃, c₄, c₅, by simp only [Subfield.smul_def, smul_eq_mul]; ring⟩

end R9_laurentTwo

open DiazModulus R9_laurentTwo Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) :
    LinearIndependent (↥Qbar) ![1, u] ∧ LinearIndependent (↥Qbar) ![u⁻¹, 1, u ^ 3] ∧
      Submodule.span Qbar (Set.range fun ij : Fin 2 × Fin 3 => ![1, u] ij.1 * ![u⁻¹, 1, u ^ 3] ij.2) = Submodule.span Qbar ({u⁻¹, 1, u, u ^ 3, u ^ 4} : Set ℂ) ∧
      u ^ 2 ∉ Submodule.span Qbar ({u⁻¹, 1, u, u ^ 3, u ^ 4} : Set ℂ) ∧ (u ^ 2)⁻¹ ∉ Submodule.span Qbar ({u⁻¹, 1, u, u ^ 3, u ^ 4} : Set ℂ) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar ({u⁻¹, 1, u, u ^ 3, u ^ 4} : Set ℂ) := by
  have hu0 := ne_zero_of_not_mem hu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `s + t u = 0`
    rw [LinearIndependent.pair_iff]
    intro s t h
    have hP := aeval_eq_zero hu (P := C s + C t * X)
      (by simpa [Subfield.smul_def, algebraMap_coe] using h)
    have h0 := congrArg (coeff · 0) hP
    have h1 := congrArg (coeff · 1) hP
    simp [coeff_C, coeff_X] at h0 h1
    exact ⟨h0, h1⟩
  · -- `a u⁻¹ + b + c u³ = 0`, times `u`
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Subfield.smul_def, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, smul_eq_mul] at hg
    have hP := aeval_eq_zero hu (P := C (g 0) + C (g 1) * X + C (g 2) * X ^ 4)
      (by
        simp only [map_add, map_mul, aeval_C, aeval_X, aeval_X_pow, algebraMap_coe]
        have : u * ((g 0 : ℂ) * u⁻¹ + g 1 * 1 + g 2 * u ^ 3) = 0 := by rw [hg, mul_zero]
        rw [← this]; field_simp)
    have h0 := congrArg (coeff · 0) hP
    have h1 := congrArg (coeff · 1) hP
    have h4 := congrArg (coeff · 4) hP
    simp [coeff_C, coeff_X, coeff_X_pow] at h0 h1 h4
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h4
  · apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨i, j⟩, rfl⟩
      fin_cases i <;> fin_cases j <;>
        refine Submodule.subset_span ?_ <;> simp [hu0, ← pow_succ']
    · refine Submodule.span_le.2 ?_
      have hm : ∀ (i : Fin 2) (j : Fin 3) (t : ℂ), ![1, u] i * ![u⁻¹, 1, u ^ 3] j = t →
          t ∈ Submodule.span Qbar (Set.range fun ij : Fin 2 × Fin 3 =>
            ![1, u] ij.1 * ![u⁻¹, 1, u ^ 3] ij.2) :=
        fun i j t h => Submodule.subset_span ⟨(i, j), h⟩
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      refine ⟨hm 0 0 _ (by simp), hm 0 1 _ (by simp), hm 1 1 _ (by simp), hm 0 2 _ (by simp),
        hm 1 2 _ (by simp; ring)⟩
  · intro h
    obtain ⟨c₁, c₂, c₃, c₄, c₅, hc⟩ := mem_span5 h
    have hP := aeval_eq_zero hu
      (P := C c₁ + C c₂ * X + C c₃ * X ^ 2 - X ^ 3 + C c₄ * X ^ 4 + C c₅ * X ^ 5)
      (by
        simp only [map_add, map_sub, map_mul, aeval_C, aeval_X, aeval_X_pow, algebraMap_coe]
        have : u * (u ^ 2 - ((c₁ : ℂ) * u⁻¹ + c₂ * 1 + c₃ * u + c₄ * u ^ 3 + c₅ * u ^ 4)) = 0 := by
          rw [← hc, sub_self, mul_zero]
        rw [← neg_eq_zero, ← this]; field_simp; ring)
    have h3 := congrArg (coeff · 3) hP
    simp [coeff_X_pow] at h3
  · intro h
    obtain ⟨c₁, c₂, c₃, c₄, c₅, hc⟩ := mem_span5 h
    have hP := aeval_eq_zero hu
      (P := 1 - (C c₁ * X + C c₂ * X ^ 2 + C c₃ * X ^ 3 + C c₄ * X ^ 5 + C c₅ * X ^ 6))
      (by
        simp only [map_add, map_sub, map_one, map_mul, aeval_C, aeval_X, aeval_X_pow,
          algebraMap_coe]
        have : u ^ 2 * ((u ^ 2)⁻¹ - ((c₁ : ℂ) * u⁻¹ + c₂ * 1 + c₃ * u + c₄ * u ^ 3 + c₅ * u ^ 4))
            = 0 := by
          rw [← hc, sub_self, mul_zero]
        rw [← this]; field_simp)
    have h0 := congrArg (coeff · 0) hP
    simp [coeff_C, coeff_X, coeff_X_pow, coeff_one] at h0
  · intro b hb hb0 h
    obtain ⟨c₁, c₂, c₃, c₄, c₅, hc⟩ := mem_span5 h
    have hub : u - b ≠ 0 := fun h' => hu (sub_eq_zero.1 h' ▸ hb)
    have hP := aeval_eq_zero hu
      (P := X - (X - C ⟨b, hb⟩) * (C c₁ + C c₂ * X + C c₃ * X ^ 2 + C c₄ * X ^ 4 + C c₅ * X ^ 5))
      (by
        simp only [map_add, map_sub, map_mul, aeval_C, aeval_X, aeval_X_pow, algebraMap_coe]
        have : u * (u - b) * ((u - b)⁻¹ -
            ((c₁ : ℂ) * u⁻¹ + c₂ * 1 + c₃ * u + c₄ * u ^ 3 + c₅ * u ^ 4)) = 0 := by
          rw [← hc, sub_self, mul_zero]
        rw [← this]; field_simp)
    have hb' := congrArg (eval (⟨b, hb⟩ : ↥Qbar)) hP
    simp only [eval_sub, eval_mul, eval_X, eval_C, sub_self, zero_mul, sub_zero, eval_zero] at hb'
    exact hb0 (congrArg Subtype.val hb')
