-- Prove2me | solution 1 for DiazModulus.quadratic_complement_multiplication_matrix
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:32:35.173018+00:00
-- url     : https://prove2.me/submissions/30f43928-801d-4adf-916e-e45ca335dc13

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The matrix of multiplication by `k` on `W / H₀`

Let `W = span_Q̄ (1, u, u⁻¹, g₀, g₁)` and `k gⱼ ∈ W`. Peeling the five generators off with
`Submodule.mem_span_insert` (and `mem_span_singleton` for the last one) writes
`k gⱼ = aⱼ + bⱼ u + cⱼ u⁻¹ + dⱼ g₀ + eⱼ g₁` with coefficients in `Q̄`. The matrix is
`T = [[d₀, d₁], [e₀, e₁]]`, and the `H₀` part is `(cⱼ + aⱼ X + bⱼ X²)(u) / u`, since `u ≠ 0`
(`0 ∈ Q̄`, `u ∉ Q̄`); the polynomial has degree at most 2 by `natDegree_quadratic_le`.
The dimension hypothesis is not needed for the existence of `T` and `R`. -/

namespace R20_mulmat

open DiazModulus Polynomial

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem sm (a : ↥Qbar) (z : ℂ) : a • z = (a : ℂ) * z := rfl

theorem coeffs5 {u x : ℂ} {g : Fin 2 → ℂ}
    (hx : x ∈ Submodule.span Qbar ({1, u, u⁻¹, g 0, g 1} : Set ℂ)) :
    ∃ a b c d e : ↥Qbar, x = (a : ℂ) + b * u + c * u⁻¹ + d * g 0 + e * g 1 := by
  obtain ⟨a, z₁, h₁, rfl⟩ := Submodule.mem_span_insert.1 hx
  obtain ⟨b, z₂, h₂, rfl⟩ := Submodule.mem_span_insert.1 h₁
  obtain ⟨c, z₃, h₃, rfl⟩ := Submodule.mem_span_insert.1 h₂
  obtain ⟨d, z₄, h₄, rfl⟩ := Submodule.mem_span_insert.1 h₃
  obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.1 h₄
  exact ⟨a, b, c, d, e, by simp only [sm]; ring⟩

end R20_mulmat

open DiazModulus R20_mulmat in
open Polynomial in
theorem solution (u k : ℂ) (hu : u ∉ Qbar) (g : Fin 2 → ℂ)
    (hk : ∀ j, k * g j ∈ Submodule.span Qbar ({1, u, u⁻¹, g 0, g 1} : Set ℂ)) :
    ∃ (T : Matrix (Fin 2) (Fin 2) ↥Qbar) (R : Fin 2 → (↥Qbar)[X]), ∀ j, (R j).natDegree ≤ 2 ∧
      k * g j = aeval u (R j) / u + (T 0 j : ℂ) * g 0 + (T 1 j : ℂ) * g 1 := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)
  choose a b c d e h using fun j => coeffs5 (hk j)
  refine ⟨Matrix.of ![d, e], fun j => C (b j) * X ^ 2 + C (a j) * X + C (c j), fun j => ⟨?_, ?_⟩⟩
  · exact natDegree_quadratic_le
  · rw [h j]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_mul,
      aeval_C, aeval_X, map_pow, am]
    field_simp
    ring
