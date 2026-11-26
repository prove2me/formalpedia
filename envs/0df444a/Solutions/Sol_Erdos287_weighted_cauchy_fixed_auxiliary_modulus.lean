-- Prove2me | solution 1 for Erdos287.weighted_cauchy_fixed_auxiliary_modulus
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T19:03:04.808314+00:00
-- url     : https://prove2.me/submissions/fdc4800a-a6ed-4815-bb28-e1492c208207

import Mathlib

open Finset

set_option autoImplicit false

/-- Weighted Cauchy–Schwarz keeps the auxiliary modulus fixed in every
square of the inner discrepancy. -/
theorem solution {ι : Type*} (Q : Finset ℕ) (I : Finset ι)
    (hQ : ∀ q ∈ Q, 0 < q) (γ : ℕ → ℝ) (α : ι → ℝ) (E : ℕ → ι → ℝ) :
    (∑ q ∈ Q, γ q * ∑ i ∈ I, α i * E q i) ^ 2 ≤
      (∑ q ∈ Q, (γ q) ^ 2 / (q : ℝ)) * (∑ i ∈ I, (α i) ^ 2) *
        ∑ q ∈ Q, (q : ℝ) * ∑ i ∈ I, (E q i) ^ 2 := by
  classical
  let r (p : ℕ × ι) := γ p.1 * (α p.2 * E p.1 p.2)
  let f (p : ℕ × ι) := (γ p.1) ^ 2 / (p.1 : ℝ) * (α p.2) ^ 2
  let g (p : ℕ × ι) := (p.1 : ℝ) * (E p.1 p.2) ^ 2
  have hf (p : ℕ × ι) (_hp : p ∈ Q ×ˢ I) : 0 ≤ f p := by dsimp [f]; positivity
  have hg (p : ℕ × ι) (_hp : p ∈ Q ×ˢ I) : 0 ≤ g p := by dsimp [g]; positivity
  have hr (p : ℕ × ι) (hp : p ∈ Q ×ˢ I) : (r p) ^ 2 = f p * g p := by
    have hq : (p.1 : ℝ) ≠ 0 := by exact_mod_cast (hQ p.1 (mem_product.mp hp).1).ne'
    dsimp only [r, f, g]
    field_simp
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul (Q ×ˢ I) hf hg (fun p hp => (hr p hp).le)
  simp only [sum_product, r, f, g, ← mul_sum, ← sum_mul] at hc
  exact hc

