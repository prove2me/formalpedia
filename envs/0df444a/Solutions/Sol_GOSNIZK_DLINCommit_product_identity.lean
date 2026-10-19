-- Prove2me | solution 1 for GOSNIZK.DLINCommit.product_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:26:43.23566+00:00
-- url     : https://prove2.me/submissions/135e489d-6c3e-4ca4-9fa6-70f4998066bb

import Mathlib
set_option autoImplicit false

theorem solution (p : ℕ) [Fact p.Prime]
    (r₀ s₀ t₀ r₁ s₁ t₁ m₁₁ m₁₂ m₁₃ m₂₁ m₂₂ m₂₃ : ZMod p)
    (e₁ : m₁₁ = r₀ * r₁) (e₂ : m₂₂ = s₀ * s₁) (e₃ : m₁₃ + m₂₃ = t₀ * t₁)
    (e₄ : m₁₂ + m₂₁ = r₀ * s₁ + s₀ * r₁)
    (e₅ : m₁₃ + (m₁₁ + m₂₁) = r₀ * t₁ + t₀ * r₁)
    (e₆ : m₂₃ + (m₁₂ + m₂₂) = s₀ * t₁ + t₀ * s₁) :
    (r₀ + s₀ - t₀) * (r₁ + s₁ - t₁) =
        r₀ * r₁ + r₀ * s₁ + s₀ * r₁ + s₀ * s₁ + t₀ * t₁ - (r₀ * t₁ + t₀ * r₁ + s₀ * t₁ + t₀ * s₁) ∧
      r₀ * r₁ + r₀ * s₁ + s₀ * r₁ + s₀ * s₁ + t₀ * t₁ - (r₀ * t₁ + t₀ * r₁ + s₀ * t₁ + t₀ * s₁) =
        m₁₁ + m₁₂ + m₂₁ + m₂₂ + (m₁₃ + m₂₃) - m₁₃ - (m₁₁ + m₂₁) - m₂₃ - (m₁₂ + m₂₂) ∧
      m₁₁ + m₁₂ + m₂₁ + m₂₂ + (m₁₃ + m₂₃) - m₁₃ - (m₁₁ + m₂₁) - m₂₃ - (m₁₂ + m₂₂) = 0 ∧
      (t₀ = r₀ + s₀ ∨ t₁ = r₁ + s₁) := by
  have h2 : r₀ * r₁ + r₀ * s₁ + s₀ * r₁ + s₀ * s₁ + t₀ * t₁ - (r₀ * t₁ + t₀ * r₁ + s₀ * t₁ + t₀ * s₁) =
        m₁₁ + m₁₂ + m₂₁ + m₂₂ + (m₁₃ + m₂₃) - m₁₃ - (m₁₁ + m₂₁) - m₂₃ - (m₁₂ + m₂₂) := by
    linear_combination (-1 : ZMod p) * e₁ - e₂ - e₃ - e₄ + e₅ + e₆
  have h1 : (r₀ + s₀ - t₀) * (r₁ + s₁ - t₁) =
        r₀ * r₁ + r₀ * s₁ + s₀ * r₁ + s₀ * s₁ + t₀ * t₁ - (r₀ * t₁ + t₀ * r₁ + s₀ * t₁ + t₀ * s₁) := by ring
  have h3 : m₁₁ + m₁₂ + m₂₁ + m₂₂ + (m₁₃ + m₂₃) - m₁₃ - (m₁₁ + m₂₁) - m₂₃ - (m₁₂ + m₂₂) = 0 := by
    ring
  refine ⟨h1, h2, h3, ?_⟩
  have h0 : (r₀ + s₀ - t₀) * (r₁ + s₁ - t₁) = 0 := by rw [h1, h2, h3]
  rcases mul_eq_zero.mp h0 with h | h
  · left; linear_combination -h
  · right; linear_combination -h
