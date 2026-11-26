-- Prove2me | solution 1 for Erdos287.dispersion_quotient_congruence
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T04:26:49.310133+00:00
-- url     : https://prove2.me/submissions/8188c1c0-6012-4fa7-a7b1-fed3384f4db8

import Mathlib

set_option autoImplicit false

/-- The dispersion congruence after adjoining a shared modulus, with no
coprimality requirement between the shared modulus and the other factors. -/
theorem solution (a x n₁ n₂ r₁ r₂ s k : ℤ)
    (hs : s ≠ 0) (hdiff : n₁ - n₂ = s * k)
    (h₁ : r₁ * s ∣ x * n₁ - a) (h₂ : r₂ * s ∣ x * n₂ - a) :
    ∃ l : ℤ, x * n₁ = a + r₁ * s * l ∧ r₂ * n₁ ∣ r₁ * n₂ * l - a * k := by
  obtain ⟨l, hl⟩ := h₁
  obtain ⟨j, hj⟩ := h₂
  refine ⟨l, by linarith only [hl], j, ?_⟩
  apply mul_left_cancel₀ hs
  calc
    s * (r₁ * n₂ * l - a * k) = n₂ * (r₁ * s * l) - a * (s * k) := by ring
    _ = n₂ * (x * n₁ - a) - a * (n₁ - n₂) := by rw [← hl, ← hdiff]
    _ = n₁ * (x * n₂ - a) := by ring
    _ = s * (r₂ * n₁ * j) := by rw [hj]; ring

