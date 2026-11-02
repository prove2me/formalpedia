-- Prove2me | solution 1 for DiazModulus.u_multiplier_space_le_span_no_degree_one_no_visible_element
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T09:33:28.033597+00:00
-- url     : https://prove2.me/submissions/94f74c62-693f-4da0-8215-3dfc6b8b9b4e

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A `u`-multiplier space inside `span(1, u⁻¹)` rules out degree one and every `t_x`

Let `u ∉ Q̄`, so `u` is transcendental over `Q̄`, and let `W ∋ u, u⁻¹` be such that every `f ∈ W` with
`u f ∈ W` lies in `span(1, u⁻¹)`.
* **No degree-one configuration.** Three free vectors `t j` with `t j, u t j ∈ W` would lie in the
  two-dimensional `span(1, u⁻¹)` (`linearIndependent_le_span_finset`).
* **No `t_x`.** If `u² ∈ W` take `f = u`; if `u⁻² ∈ W` take `f = u⁻²` (then `u f = u⁻¹`); if
  `(u − a)⁻¹ ∈ W` with `a ∈ Q̄ ∖ 0` take `f = (u − a)⁻¹ − u⁻¹`, so `u f = a (u − a)⁻¹`. In each case
  `f ∈ W`, `u f ∈ W`, and `f = c + d u⁻¹` clears to a polynomial relation of degree `≤ 2` in `u` with a
  non-zero coefficient, which transcendence forbids. `1 ∈ W` is not needed.
-/

namespace R21b_G

open DiazModulus Polynomial

theorem tr_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem smul_def' (c : ↥Qbar) (z : ℂ) : c • z = (c : ℂ) * z := rfl

/-- `1, u, u²` are free over `Q̄`. -/
theorem quad {u : ℂ} (hu : u ∉ Qbar) (a₀ a₁ a₂ : ↥Qbar)
    (h : (a₀ : ℂ) + a₁ * u + a₂ * u ^ 2 = 0) : a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 := by
  have hP := transcendental_iff.1 (tr_of_not_mem hu) (C a₀ + C a₁ * X + C a₂ * X ^ 2) (by
    simpa only [map_add, map_mul, map_pow, aeval_C, aeval_X, am] using h)
  exact ⟨by simpa using congrArg (coeff · 0) hP, by simpa using congrArg (coeff · 1) hP,
    by simpa using congrArg (coeff · 2) hP⟩

theorem span2 {u f : ℂ} (hf : f ∈ Submodule.span Qbar ({1, u⁻¹} : Set ℂ)) :
    ∃ c d : ↥Qbar, f = (c : ℂ) + d * u⁻¹ := by
  obtain ⟨c, w, hw, rfl⟩ := Submodule.mem_span_insert.1 hf
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hw
  exact ⟨c, d, by rw [smul_def', smul_def', mul_one]⟩

end R21b_G

open DiazModulus R21b_G in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ)
    (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (hZ : ∀ f ∈ W, u * f ∈ W → f ∈ Submodule.span Qbar ({1, u⁻¹} : Set ℂ)) :
    ¬ (∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ W ∧ u * t j ∈ W) ∧
    ¬ (u ^ 2 ∈ W ∨ (u ^ 2)⁻¹ ∈ W ∨ ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ W) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)
  refine ⟨?_, ?_⟩
  · rintro ⟨t, ht, hW⟩
    have h := linearIndependent_le_span_aux' t ht (({1, u⁻¹} : Finset ℂ) : Set ℂ) (by
      rintro _ ⟨j, rfl⟩
      exact SetLike.mem_coe.2 (by
        simpa only [Finset.coe_insert, Finset.coe_singleton] using hZ _ (hW j).1 (hW j).2))
    simp only [Finset.coe_sort_coe, Fintype.card_coe, Fintype.card_fin] at h
    have := Finset.card_le_two (a := (1 : ℂ)) (b := u⁻¹)
    omega
  · rintro (h | h | ⟨a, ha, ha0, h⟩)
    · obtain ⟨c, d, e⟩ := span2 (hZ u hu1 (by rwa [← sq]))
      have e' : (d : ℂ) + c * u + (-1 : ↥Qbar) * u ^ 2 = 0 := by
        field_simp at e
        push_cast
        linear_combination -e
      exact one_ne_zero (neg_eq_zero.1 (quad hu _ _ _ e').2.2)
    · obtain ⟨c, d, e⟩ := span2 (hZ _ h (by rwa [show u * (u ^ 2)⁻¹ = u⁻¹ by field_simp]))
      have e' : ((-1 : ↥Qbar) : ℂ) + d * u + c * u ^ 2 = 0 := by
        field_simp at e
        push_cast
        linear_combination -e
      exact one_ne_zero (neg_eq_zero.1 (quad hu _ _ _ e').1)
    · lift a to ↥Qbar using ha
      have hua : u - a ≠ 0 := fun h' => hu (by rw [sub_eq_zero.1 h']; exact a.2)
      have hf : (u - a)⁻¹ - u⁻¹ ∈ W := sub_mem h hui
      have huf : u * ((u - a)⁻¹ - u⁻¹) ∈ W := by
        have e : u * ((u - a)⁻¹ - u⁻¹) = a • (u - a)⁻¹ := by
          rw [Subfield.smul_def, smul_eq_mul]
          field_simp
          ring
        rw [e]
        exact W.smul_mem a h
      obtain ⟨c, d, e⟩ := span2 (hZ _ hf huf)
      have e' : ((-d * a - a : ↥Qbar) : ℂ) + (d - c * a : ↥Qbar) * u + c * u ^ 2 = 0 := by
        field_simp at e
        push_cast
        linear_combination -e
      obtain ⟨h0, h1, h2⟩ := quad hu _ _ _ e'
      subst h2
      have hd : d = 0 := by simpa using h1
      subst hd
      exact ha0 (by simpa using h0)
