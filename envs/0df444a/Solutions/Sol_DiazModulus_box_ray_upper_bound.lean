-- Prove2me | solution 1 for DiazModulus.box_ray_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:09:29.692986+00:00
-- url     : https://prove2.me/submissions/bfd88dd6-6d5b-47d3-a683-1449bed3aad3

import Mathlib

open Complex ComplexConjugate

/-! # The box count along the ray `v ↦ v · D`, from above

Both products are over constant factors, so they are powers: `(vD₀ + 1)^{d₀} (2vD₁ + 1)^{d₁}`.
Since `D₀, D₁ ≥ 1`, each factor is at most the matching factor of the right side:
`vD₀ + 1 ≤ (v + 1) D₀` and `2vD₁ + 1 ≤ (v + 1)(2D₁)`. Monotonicity of powers and products
(`Nat.pow_le_pow_left`, `Nat.mul_le_mul`) and `mul_pow`, `pow_add` regroup the factors `(v + 1)`
into `(v + 1)^{d₀ + d₁}`. -/

namespace C11_A2a

theorem factor_le (v D : ℕ) (h : 1 ≤ D) : v * D + 1 ≤ (v + 1) * D := by nlinarith

end C11_A2a

open C11_A2a in
theorem solution {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (D₀ D₁ : ℕ) (h0 : 1 ≤ D₀) (h1 : 1 ≤ D₁) (v : ℕ) :
    (∏ _h : A₀, (v * D₀ + 1)) * ∏ _i : A₁, (2 * (v * D₁) + 1)
      ≤ (v + 1) ^ (Fintype.card A₀ + Fintype.card A₁) * (D₀ ^ Fintype.card A₀ * (2 * D₁) ^ Fintype.card A₁) := by
  simp only [Finset.prod_const, Finset.card_univ]
  have e0 := factor_le v D₀ h0
  have e1 : 2 * (v * D₁) + 1 ≤ (v + 1) * (2 * D₁) := by
    have := factor_le v (2 * D₁) (by omega)
    rw [show v * (2 * D₁) = 2 * (v * D₁) by ring] at this
    exact this
  calc (v * D₀ + 1) ^ Fintype.card A₀ * (2 * (v * D₁) + 1) ^ Fintype.card A₁
      ≤ ((v + 1) * D₀) ^ Fintype.card A₀ * ((v + 1) * (2 * D₁)) ^ Fintype.card A₁ :=
        Nat.mul_le_mul (Nat.pow_le_pow_left e0 _) (Nat.pow_le_pow_left e1 _)
    _ = _ := by rw [mul_pow, mul_pow, pow_add]; ring
