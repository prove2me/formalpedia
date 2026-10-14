-- Prove2me | solution 1 for DiazModulus.quadratic_over_ratio_of_mem_progression_pair_span
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T07:34:22.065973+00:00
-- url     : https://prove2.me/submissions/28b5ddfb-4cec-4092-9011-698eeb8442db

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # `u` is quadratic over `K(h)` when `1, u, u⁻¹` lie in `c·⟨1, h, h², k, hk⟩`

Write `K = Q̄` and `S = span_K {c, ch, ch², ck, chk}`. Every element of `S` reads
`c (a(h) + k b(h))` with `a, b ∈ K[X]` (`deg a ≤ 2`, `deg b ≤ 1`), by repeated
`Submodule.mem_span_insert`. So `1 = c (a₀(h) + k b₀(h))`, `u = c (a₁(h) + k b₁(h))`,
`u⁻¹ = c (a₂(h) + k b₂(h))`. Put `Dᵢⱼ = aᵢ bⱼ − aⱼ bᵢ ∈ K[X]`. The vectors `(aᵢ, bᵢ)` satisfy the
Plücker identity `D₁₂ (a₀, b₀) − D₀₂ (a₁, b₁) + D₀₁ (a₂, b₂) = 0`; evaluating at `h` and pairing
with `(c, ck)` gives `D₁₂(h) − D₀₂(h) u + D₀₁(h) u⁻¹ = 0`, i.e.
`−D₀₂(h) u² + D₁₂(h) u + D₀₁(h) = 0` after multiplying by `u ≠ 0`. If `D₀₁ ≠ 0` this is the
required non-trivial relation. If `D₀₁ = 0`, then `a₀(h) b₁(h) = a₁(h) b₀(h)` and a direct
computation gives `a₀(h) u = a₁(h)` and `b₀(h) u = b₁(h)`; one of `a₀, b₀` is a non-zero
polynomial (otherwise `1 = 0`), which yields a non-trivial relation of degree one in `u`.
The argument uses only `u ≠ 0`; the hypotheses `c ≠ 0` and `h ∉ K` are not needed.
-/

namespace R14_degree_quad

open DiazModulus Polynomial

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

/-- Unpacking membership in `span_K {c, ch, ch², ck, chk}`. -/
theorem unpack {c h k x : ℂ}
    (hx : x ∈ Submodule.span Qbar ({c, c * h, c * h ^ 2, c * k, c * h * k} : Set ℂ)) :
    ∃ a b : (↥Qbar)[X], x = c * (aeval h a + k * aeval h b) := by
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hx
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, w₃, hw₃, rfl⟩ := Submodule.mem_span_insert.1 hw₂
  obtain ⟨c₄, w₄, hw₄, rfl⟩ := Submodule.mem_span_insert.1 hw₃
  obtain ⟨c₅, rfl⟩ := Submodule.mem_span_singleton.1 hw₄
  refine ⟨C c₁ + C c₂ * X + C c₃ * X ^ 2, C c₄ + C c₅ * X, ?_⟩
  simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am, Subfield.smul_def, smul_eq_mul]
  ring

end R14_degree_quad

open DiazModulus R14_degree_quad Polynomial in
theorem solution
    (u : ℂ) (hu : u ∉ Qbar) (c h k : ℂ) (hc : c ≠ 0) (hh : h ∉ Qbar)
    (h1 : (1 : ℂ) ∈ Submodule.span Qbar ({c, c * h, c * h ^ 2, c * k, c * h * k} : Set ℂ)) (hu1 : u ∈ Submodule.span Qbar ({c, c * h, c * h ^ 2, c * k, c * h * k} : Set ℂ)) (hui : u⁻¹ ∈ Submodule.span Qbar ({c, c * h, c * h ^ 2, c * k, c * h * k} : Set ℂ)) :
    ∃ A B C : Polynomial ↥Qbar, (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) ∧
      Polynomial.aeval h A * u ^ 2 + Polynomial.aeval h B * u + Polynomial.aeval h C = 0 := by
  have hu0 : u ≠ 0 := fun e => hu (e ▸ zero_mem _)
  have hinv : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
  obtain ⟨a₀, b₀, e₀⟩ := unpack h1
  obtain ⟨a₁, b₁, e₁⟩ := unpack hu1
  obtain ⟨a₂, b₂, e₂⟩ := unpack hui
  by_cases hD : a₀ * b₁ - a₁ * b₀ = 0
  · -- degenerate case: a relation of degree one in `u`
    have hd : aeval h a₀ * aeval h b₁ = aeval h a₁ * aeval h b₀ := by
      have := congrArg (aeval h) hD
      simp only [map_sub, map_mul, map_zero] at this
      linear_combination this
    by_cases ha₀ : a₀ = 0
    · have hb₀ : b₀ ≠ 0 := by
        rintro rfl
        rw [ha₀] at e₀
        simp at e₀
      refine ⟨0, b₀, -b₁, Or.inr (Or.inl hb₀), ?_⟩
      simp only [map_zero, map_neg]
      linear_combination aeval h b₀ * e₁ - aeval h b₁ * e₀ - c * hd
    · refine ⟨0, a₀, -a₁, Or.inr (Or.inl ha₀), ?_⟩
      simp only [map_zero, map_neg]
      linear_combination aeval h a₀ * e₁ - aeval h a₁ * e₀ + c * k * hd
  · -- generic case: the Plücker relation
    refine ⟨-(a₀ * b₂ - a₂ * b₀), a₁ * b₂ - a₂ * b₁, a₀ * b₁ - a₁ * b₀, Or.inr (Or.inr hD), ?_⟩
    simp only [map_neg, map_sub, map_mul]
    linear_combination u * ((aeval h a₁ * aeval h b₂ - aeval h a₂ * aeval h b₁) * e₀ -
      (aeval h a₀ * aeval h b₂ - aeval h a₂ * aeval h b₀) * e₁ +
      (aeval h a₀ * aeval h b₁ - aeval h a₁ * aeval h b₀) * e₂) -
      (aeval h a₀ * aeval h b₁ - aeval h a₁ * aeval h b₀) * hinv
