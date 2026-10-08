-- Prove2me | solution 1 for DiazModulus.circle_point_conjugate_pair_extension_excludes_squares_and_reciprocals
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-06T08:26:22.528264+00:00
-- url     : https://prove2.me/submissions/0b8283f2-7cc5-417a-a5ef-d7e8f10617f9

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-!
# A conjugate-pair extension excludes `u²`, `ū²` and every `(u − b)⁻¹`

Let `u ∉ Q̄` with `ρ = u ū` algebraic, `a ∈ Q̄` non-zero, and either `z = u/(u² − a)` (F1) or
`a ā = ρ²` and `z = u/(u² − a)²` (F2). Then `W = Q̄ + Q̄u + Q̄ū + Q̄z + Q̄z̄` contains none of `u²`,
`ū²`, `(u − b)⁻¹` for `b ∈ Q̄` non-zero.

Both cases have the shape `z Q₁(u²) = u R₁(u²)`, `z̄ Q₂(u²) = u R₂(u²)` with `Q₁(0), Q₂(0) ≠ 0`
(`excl`):
* F1: `Q₁ = X − a`, `R₁ = 1`, `Q₂ = X − a'`, `R₂ = κ`, with `ā a' = ρ²` and `ā κ = −ρ`;
* F2: `Q₁ = Q₂ = (X − a)²`, `R₁ = 1`, `R₂ = κ X`, with `ā² κ = ρ`.

Write `w ∈ W` in coordinates `c₁, …, c₅` and clear denominators: this gives `A(u²) + u B(u²) = 0`,
hence `A = B = 0` since `u` is transcendental over `Q̄` (`even_odd`).
* `w = u²`: the odd part is `B = (X − c₁) Q₁ Q₂ ≠ 0`.
* `w = ū²`: the even part is `A = (ρ² − c₁ X) Q₁ Q₂`, and `A(0) = ρ² Q₁(0) Q₂(0) ≠ 0`.
* `w = (u − b)⁻¹ = (u + b)/(u² − b²)`: the odd part is `B = Q₁ Q₂ (b − c₁ (X − b²))`, and the last
  factor takes the value `b ≠ 0` at `b²`.
-/

namespace R5_excl

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

/-- `Q̄` is stable under complex conjugation. -/
theorem conj_mem_Qbar {z : ℂ} (hz : z ∈ Qbar) : conj z ∈ Qbar :=
  mem_Qbar_iff.2 ((mem_Qbar_iff.1 hz).algHom
    ((Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ))

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

end R5_excl

open DiazModulus R5_excl Polynomial in
theorem solution (u a z : ℂ)
    (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) (ha : a ∈ Qbar) (ha0 : a ≠ 0)
    (hz : (a * conj a ≠ (u * conj u) ^ 2 ∧ z = u / (u ^ 2 - a)) ∨
      (a * conj a = (u * conj u) ^ 2 ∧ z = u / (u ^ 2 - a) ^ 2)) :
    u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) ∧
      conj u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) := by
  have hu0 := ne_zero_of_not_mem hu
  obtain ⟨ρ, hρ'⟩ : ∃ ρ : ↥Qbar, u * conj u = ρ := ⟨⟨_, mem_Qbar_iff.2 hρ⟩, rfl⟩
  have hρc : (ρ : ℂ) ≠ 0 := by rw [← hρ']; exact mul_ne_zero hu0 ((_root_.map_ne_zero _).2 hu0)
  have hρ0 : ρ ≠ 0 := by rintro rfl; exact hρc rfl
  obtain ⟨α, rfl⟩ : ∃ α : ↥Qbar, (α : ℂ) = a := ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨αb, hαb⟩ : ∃ αb : ↥Qbar, conj (α : ℂ) = αb := ⟨⟨_, conj_mem_Qbar α.2⟩, rfl⟩
  have hα0 : α ≠ 0 := by rintro rfl; exact ha0 rfl
  have hαb0 : (αb : ℂ) ≠ 0 := by rw [← hαb]; exact (_root_.map_ne_zero _).2 ha0
  have hv : u ^ 2 - α ≠ 0 := sq_sub_ne hu α
  have hcv : conj u ^ 2 - αb ≠ 0 := by
    rw [← hαb, ← map_pow, ← map_sub]; exact (_root_.map_ne_zero _).2 hv
  rcases hz with ⟨-, rfl⟩ | ⟨haa, rfl⟩
  · -- F1: `z̄ (u² − a') = κ u` with `ā a' = ρ²` and `ā κ = −ρ`
    have hcz : conj (u / (u ^ 2 - α)) * (conj u ^ 2 - αb) = conj u := by
      simp only [map_div₀, map_sub, map_pow, hαb]; exact div_mul_cancel₀ _ hcv
    obtain ⟨α', hα'⟩ : ∃ α' : ↥Qbar, (αb : ℂ) * α' = (ρ : ℂ) ^ 2 :=
      ⟨ρ ^ 2 / αb, by push_cast; field_simp⟩
    obtain ⟨κ, hκ⟩ : ∃ κ : ↥Qbar, (αb : ℂ) * κ = -ρ := ⟨-ρ / αb, by push_cast; field_simp⟩
    have hα'0 : α' ≠ 0 := by
      rintro rfl
      exact pow_ne_zero 2 hρc (by rw [← hα']; simp)
    refine excl hu hρ0 hρ' (Q₁ := X - C α) (R₁ := 1) (Q₂ := X - C α') (R₂ := C κ)
      (by simpa using hα0) (by simpa using hα'0) ?_ ?_
    · simp only [map_sub, aeval_X, aeval_C, am, map_one, mul_one]
      exact div_mul_cancel₀ _ hv
    · simp only [map_sub, aeval_X, aeval_C, am]
      refine mul_left_cancel₀ hαb0 ?_
      linear_combination (conj (u / (u ^ 2 - α)) * (u * conj u + ρ) - u) * hρ' - u ^ 2 * hcz -
        conj (u / (u ^ 2 - α)) * hα' - u * hκ
  · -- F2: `z̄ (u² − a)² = κ u³` with `ā² κ = ρ`
    have haa' : (α : ℂ) * αb = (ρ : ℂ) ^ 2 := by rw [← hαb, haa, hρ']
    have hcz : conj (u / (u ^ 2 - α) ^ 2) * (conj u ^ 2 - αb) ^ 2 = conj u := by
      simp only [map_div₀, map_sub, map_pow, hαb]; exact div_mul_cancel₀ _ (pow_ne_zero 2 hcv)
    have hX : (αb : ℂ) * (u ^ 2 - α) = -u ^ 2 * (conj u ^ 2 - αb) := by
      linear_combination (u * conj u + ρ) * hρ' - haa'
    obtain ⟨κ, hκ⟩ : ∃ κ : ↥Qbar, (αb : ℂ) ^ 2 * κ = ρ := ⟨ρ / αb ^ 2, by push_cast; field_simp⟩
    refine excl hu hρ0 hρ' (Q₁ := (X - C α) ^ 2) (R₁ := 1) (Q₂ := (X - C α) ^ 2)
      (R₂ := C κ * X) (by simpa using hα0) (by simpa using hα0) ?_ ?_
    · simp only [map_pow, map_sub, aeval_X, aeval_C, am, map_one, mul_one]
      exact div_mul_cancel₀ _ (pow_ne_zero 2 hv)
    · simp only [map_pow, map_sub, map_mul, aeval_X, aeval_C, am]
      refine mul_left_cancel₀ (pow_ne_zero 2 hαb0) ?_
      linear_combination conj (u / (u ^ 2 - α) ^ 2) *
          (αb * (u ^ 2 - α) - u ^ 2 * (conj u ^ 2 - αb)) * hX +
        u ^ 3 * hρ' + u ^ 4 * hcz - u ^ 3 * hκ

#print axioms solution
