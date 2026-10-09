-- Prove2me | solution 1 for DiazModulus.circle_point_two_pole_extension_excludes_squares_and_reciprocals
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T09:05:07.082796+00:00
-- url     : https://prove2.me/submissions/c992e7c0-5bee-4c89-9ede-0a6499662fb3

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-!
# A two-pole extension excludes `u²`, `ū²` and every `(u − b)⁻¹`

Let `u ∉ Q̄` with `ρ = u ū` algebraic, and `a₁ ≠ a₂` non-zero algebraic numbers. Then
`W = Q̄ + Q̄u + Q̄ū + Q̄z₁ + Q̄z₂`, with `zᵢ = u/(u² − aᵢ)`, contains none of `u²`, `ū²`,
`(u − b)⁻¹` for `b ∈ Q̄` non-zero.

Both `zᵢ` have the shape `zᵢ Qᵢ(u²) = u Rᵢ(u²)` with `Qᵢ = X − aᵢ`, `Rᵢ = 1`, and
`Qᵢ(0) = −aᵢ ≠ 0` (`excl`). Write `w ∈ W` in coordinates `c₁, …, c₅` and clear denominators,
using `ū = ρ/u`: this gives `A(u²) + u B(u²) = 0` with `A, B ∈ Q̄[X]`, hence `A = B = 0`, since
`u` is transcendental over `Q̄` and `u ↦ −u` separates even and odd parts (`even_odd`).
* `w = u²`: the odd part is `B = (X − c₁) Q₁ Q₂ ≠ 0`.
* `w = ū²`: the even part is `A = (ρ² − c₁ X) Q₁ Q₂`, and `A(0) = ρ² Q₁(0) Q₂(0) ≠ 0`.
* `w = (u − b)⁻¹ = (u + b)/(u² − b²)`: the odd part is `B = Q₁ Q₂ (b − c₁ (X − b²))`, and the
  last factor takes the value `b ≠ 0` at `b²`.
-/

namespace R7_twoPoleExcl

open DiazModulus Polynomial

/-! ## Transcendence of `u` and `u²` over `Q̄` -/

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem ne_zero_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : u ≠ 0 :=
  fun h => hu (h ▸ Subfield.zero_mem _)

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

/-- `u²` is transcendental over `Q̄` as well. -/
theorem sq_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval (u ^ 2) P = 0) :
    P = 0 :=
  (expand_eq_zero two_pos).1 (aeval_eq_zero hu (by rw [expand_aeval]; exact h))

theorem sq_sub_ne {u : ℂ} (hu : u ∉ Qbar) (c : ↥Qbar) : u ^ 2 - c ≠ 0 := fun h =>
  X_sub_C_ne_zero c (sq_eq_zero hu (by simp only [map_sub, aeval_X, aeval_C, am]; exact h))

/-- Even and odd parts: `A(u²) + u B(u²) = 0` forces `A = B = 0`. -/
theorem even_odd {u : ℂ} (hu : u ∉ Qbar) {A B : (↥Qbar)[X]}
    (h : aeval (u ^ 2) A + u * aeval (u ^ 2) B = 0) : A = 0 ∧ B = 0 := by
  have hP := aeval_eq_zero hu (P := expand (↥Qbar) 2 A + X * expand (↥Qbar) 2 B)
    (by rw [map_add, map_mul, expand_aeval, expand_aeval, aeval_X]; exact h)
  have h' := congrArg (aeval (-u)) hP
  rw [map_add, map_mul, expand_aeval, expand_aeval, aeval_X, neg_sq, map_zero] at h'
  have hA : aeval (u ^ 2) A = 0 := by linear_combination (h + h') / 2
  refine ⟨sq_eq_zero hu hA, sq_eq_zero hu ?_⟩
  have : u * aeval (u ^ 2) B = 0 := by linear_combination h - hA
  exact (mul_eq_zero.1 this).resolve_left (ne_zero_of_not_mem hu)

/-! ## Coordinates in `W` -/

theorem coeffs {u z zc w : ℂ} (hw : w ∈ Submodule.span Qbar ({1, u, conj u, z, zc} : Set ℂ)) :
    ∃ c₁ c₂ c₃ c₄ c₅ : ↥Qbar,
      w = (c₁ : ℂ) + c₂ * u + c₃ * conj u + c₄ * z + c₅ * zc := by
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hw
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, w₃, hw₃, rfl⟩ := Submodule.mem_span_insert.1 hw₂
  obtain ⟨c₄, w₄, hw₄, rfl⟩ := Submodule.mem_span_insert.1 hw₃
  obtain ⟨c₅, rfl⟩ := Submodule.mem_span_singleton.1 hw₄
  exact ⟨c₁, c₂, c₃, c₄, c₅, by simp only [Subfield.smul_def, smul_eq_mul]; ring⟩

/-! ## The three exclusions -/

/-- If `z Q₁(u²) = u R₁(u²)` and `z' Q₂(u²) = u R₂(u²)` with `Q₁(0), Q₂(0) ≠ 0`, then
`span_Q̄ {1, u, ū, z, z'}` contains none of `u²`, `ū²`, `(u − b)⁻¹` (`b ∈ Q̄`, `b ≠ 0`). -/
theorem excl {u z zc : ℂ} (hu : u ∉ Qbar) {ρ : ↥Qbar} (hρ0 : ρ ≠ 0) (hρ : u * conj u = ρ)
    {Q₁ R₁ Q₂ R₂ : (↥Qbar)[X]} (hQ₁ : Q₁.eval 0 ≠ 0) (hQ₂ : Q₂.eval 0 ≠ 0)
    (hz : z * aeval (u ^ 2) Q₁ = u * aeval (u ^ 2) R₁)
    (hzc : zc * aeval (u ^ 2) Q₂ = u * aeval (u ^ 2) R₂) :
    u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, z, zc} : Set ℂ) ∧
      conj u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, z, zc} : Set ℂ) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar ({1, u, conj u, z, zc} : Set ℂ) := by
  have hQ₁0 : Q₁ ≠ 0 := fun h => hQ₁ (by rw [h, eval_zero])
  have hQ₂0 : Q₂ ≠ 0 := fun h => hQ₂ (by rw [h, eval_zero])
  refine ⟨fun hw => ?_, fun hw => ?_, fun b hb hb0 hw => ?_⟩
  · -- `u²`: multiply by `u Q₁(u²) Q₂(u²)`; the odd part is `(X − c₁) Q₁ Q₂`
    obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hw
    have key := even_odd hu
      (A := -(C c₂ * X * Q₁ * Q₂ + C c₃ * C ρ * Q₁ * Q₂ + C c₄ * X * Q₂ * R₁ +
        C c₅ * X * Q₁ * R₂))
      (B := (X - C c₁) * Q₁ * Q₂) (by
        simp only [map_neg, map_add, map_sub, map_mul, aeval_X, aeval_C, am]
        linear_combination (u * aeval (u ^ 2) Q₁ * aeval (u ^ 2) Q₂) * h +
          (c₃ : ℂ) * aeval (u ^ 2) Q₁ * aeval (u ^ 2) Q₂ * hρ +
          (c₄ : ℂ) * u * aeval (u ^ 2) Q₂ * hz + (c₅ : ℂ) * u * aeval (u ^ 2) Q₁ * hzc)
    exact mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero c₁) hQ₁0) hQ₂0 key.2
  · -- `ū²`: multiply by `u² Q₁(u²) Q₂(u²)`; the even part is `(ρ² − c₁ X) Q₁ Q₂`
    obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hw
    have key := even_odd hu
      (A := (C ρ ^ 2 - C c₁ * X) * Q₁ * Q₂)
      (B := -(C c₂ * X * Q₁ * Q₂ + C c₃ * C ρ * Q₁ * Q₂ + C c₄ * X * Q₂ * R₁ +
        C c₅ * X * Q₁ * R₂)) (by
        simp only [map_neg, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, am]
        linear_combination (u ^ 2 * aeval (u ^ 2) Q₁ * aeval (u ^ 2) Q₂) * h -
          (u * conj u + ρ) * aeval (u ^ 2) Q₁ * aeval (u ^ 2) Q₂ * hρ +
          (c₃ : ℂ) * u * aeval (u ^ 2) Q₁ * aeval (u ^ 2) Q₂ * hρ +
          (c₄ : ℂ) * u ^ 2 * aeval (u ^ 2) Q₂ * hz + (c₅ : ℂ) * u ^ 2 * aeval (u ^ 2) Q₁ * hzc)
    have e := congrArg (eval 0) key.1
    simp only [eval_mul, eval_sub, eval_pow, eval_C, eval_X, mul_zero, sub_zero, eval_zero] at e
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hρ0) hQ₁) hQ₂ e
  · -- `(u − b)⁻¹`: multiply by `u Q₁(u²) Q₂(u²) (u² − b²)`; the odd part is
    -- `Q₁ Q₂ (b − c₁ (X − b²))`
    obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hw
    obtain ⟨β, rfl⟩ : ∃ β : ↥Qbar, (β : ℂ) = b := ⟨⟨b, hb⟩, rfl⟩
    have hβ0 : β ≠ 0 := by rintro rfl; exact hb0 rfl
    have hub : (u - β) * (u - β)⁻¹ = 1 :=
      mul_inv_cancel₀ (sub_ne_zero.2 fun e => hu (by rw [e]; exact β.2))
    have key := even_odd hu
      (A := X * Q₁ * Q₂ - (C c₂ * X * Q₁ * Q₂ + C c₃ * C ρ * Q₁ * Q₂ + C c₄ * X * Q₂ * R₁ +
        C c₅ * X * Q₁ * R₂) * (X - C β ^ 2))
      (B := Q₁ * Q₂ * (C β - C c₁ * (X - C β ^ 2))) (by
        simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, am]
        linear_combination (u * aeval (u ^ 2) Q₁ * aeval (u ^ 2) Q₂ * (u ^ 2 - β ^ 2)) * h -
          u * (u + β) * aeval (u ^ 2) Q₁ * aeval (u ^ 2) Q₂ * hub +
          (c₃ : ℂ) * aeval (u ^ 2) Q₁ * aeval (u ^ 2) Q₂ * (u ^ 2 - β ^ 2) * hρ +
          (c₄ : ℂ) * u * aeval (u ^ 2) Q₂ * (u ^ 2 - β ^ 2) * hz +
          (c₅ : ℂ) * u * aeval (u ^ 2) Q₁ * (u ^ 2 - β ^ 2) * hzc)
    have e := congrArg (eval (β ^ 2))
      ((mul_eq_zero.1 key.2).resolve_left (mul_ne_zero hQ₁0 hQ₂0))
    simp only [eval_sub, eval_mul, eval_pow, eval_C, eval_X, sub_self, mul_zero, sub_zero,
      eval_zero] at e
    exact hβ0 e

/-- `zᵢ = u/(u² − aᵢ)` satisfies `zᵢ Qᵢ(u²) = u Rᵢ(u²)` with `Qᵢ = X − aᵢ`, `Rᵢ = 1`. -/
theorem pole_shape {u : ℂ} (hu : u ∉ Qbar) (α : ↥Qbar) :
    u / (u ^ 2 - α) * aeval (u ^ 2) (X - C α) = u * aeval (u ^ 2) (1 : (↥Qbar)[X]) := by
  simp only [map_sub, aeval_X, aeval_C, am, map_one, mul_one]
  exact div_mul_cancel₀ _ (sq_sub_ne hu α)

theorem pole_eval {α : ↥Qbar} (hα0 : (α : ℂ) ≠ 0) : (X - C α).eval 0 ≠ 0 := by
  have : α ≠ 0 := by rintro rfl; exact hα0 rfl
  simpa using this

end R7_twoPoleExcl

open DiazModulus R7_twoPoleExcl Polynomial in
theorem solution (u a₁ a₂ : ℂ)
    (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) (ha₁ : a₁ ∈ Qbar) (ha₂ : a₂ ∈ Qbar)
    (ha₁0 : a₁ ≠ 0) (ha₂0 : a₂ ≠ 0) (ha : a₁ ≠ a₂) :
    u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, u / (u ^ 2 - a₁), u / (u ^ 2 - a₂)} : Set ℂ) ∧
      conj u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, u / (u ^ 2 - a₁), u / (u ^ 2 - a₂)} : Set ℂ) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar ({1, u, conj u, u / (u ^ 2 - a₁), u / (u ^ 2 - a₂)} : Set ℂ) := by
  have hu0 := ne_zero_of_not_mem hu
  obtain ⟨ρ, hρ'⟩ : ∃ ρ : ↥Qbar, u * conj u = ρ := ⟨⟨_, mem_Qbar_iff.2 hρ⟩, rfl⟩
  have hρc : (ρ : ℂ) ≠ 0 := by rw [← hρ']; exact mul_ne_zero hu0 ((_root_.map_ne_zero _).2 hu0)
  have hρ0 : ρ ≠ 0 := by rintro rfl; exact hρc rfl
  obtain ⟨α₁, rfl⟩ : ∃ α : ↥Qbar, (α : ℂ) = a₁ := ⟨⟨a₁, ha₁⟩, rfl⟩
  obtain ⟨α₂, rfl⟩ : ∃ α : ↥Qbar, (α : ℂ) = a₂ := ⟨⟨a₂, ha₂⟩, rfl⟩
  exact excl hu hρ0 hρ' (pole_eval ha₁0) (pole_eval ha₂0) (pole_shape hu α₁) (pole_shape hu α₂)
