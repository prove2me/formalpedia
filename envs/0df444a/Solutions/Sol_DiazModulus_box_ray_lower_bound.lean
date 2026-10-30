-- Prove2me | solution 1 for DiazModulus.box_ray_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:06:45.735441+00:00
-- url     : https://prove2.me/submissions/8583ffd8-5e80-43aa-8cf3-5185cca1cc29

import Mathlib

open Complex ComplexConjugate

/-! # The box count along the ray `u ↦ u · D`, from below

The products over `H` and `J` are over constant factors, hence the powers
`(uD₀ + 1)^{|H|}` and `(2uD₁ + 1)^{|J|}` (`Finset.prod_const`). The left side regroups as
`(uD₀)^{|H|} (uD₁)^{|J|}` (`mul_pow`, `pow_add`), and factor by factor `uD₀ ≤ uD₀ + 1` and
`uD₁ ≤ 2uD₁ + 1`; monotonicity of powers and products finishes. No hypotheses are needed. -/

namespace C11_A2b

theorem regroup (u D₀ D₁ h j : ℕ) :
    u ^ (h + j) * (D₀ ^ h * D₁ ^ j) = (u * D₀) ^ h * (u * D₁) ^ j := by
  rw [mul_pow, mul_pow, pow_add]; ring

end C11_A2b

open C11_A2b in
theorem solution {A₀ A₁ : Type*} (D₀ D₁ : ℕ) (H : Finset A₀) (J : Finset A₁) (u : ℕ) :
    u ^ (H.card + J.card) * (D₀ ^ H.card * D₁ ^ J.card)
      ≤ (∏ _h ∈ H, (u * D₀ + 1)) * ∏ _j ∈ J, (2 * (u * D₁) + 1) := by
  simp only [Finset.prod_const]
  rw [regroup]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.le_succ _) _)
    (Nat.pow_le_pow_left (by omega) _)
