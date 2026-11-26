-- Prove2me | solution 1 for Erdos287.primitive_triangle_integral_translation
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:05:34.959652+00:00
-- url     : https://prove2.me/submissions/4b798b5e-5ad6-40b6-950a-4fb01cf6f154

import Mathlib

set_option autoImplicit false

/-- Two integral solutions of a primitive system of triangle determinant
constraints differ by one integral translation along the slopes. -/
theorem solution (s₁ s₂ s₃ : ℕ) (x₁ x₂ x₃ y₁ y₂ y₃ : ℤ)
    (hprim : Nat.gcd (Nat.gcd s₁ s₂) s₃ = 1)
    (h₁₂ : (s₂ : ℤ) * x₁ - (s₁ : ℤ) * x₂ = (s₂ : ℤ) * y₁ - (s₁ : ℤ) * y₂)
    (h₁₃ : (s₃ : ℤ) * x₁ - (s₁ : ℤ) * x₃ = (s₃ : ℤ) * y₁ - (s₁ : ℤ) * y₃)
    (h₂₃ : (s₃ : ℤ) * x₂ - (s₂ : ℤ) * x₃ = (s₃ : ℤ) * y₂ - (s₂ : ℤ) * y₃) :
    ∃ t : ℤ, x₁ = y₁ + (s₁ : ℤ) * t ∧
      x₂ = y₂ + (s₂ : ℤ) * t ∧ x₃ = y₃ + (s₃ : ℤ) * t := by
  let g := Nat.gcd s₁ s₂
  let a := Nat.gcdA s₁ s₂ * Nat.gcdA g s₃
  let b := Nat.gcdB s₁ s₂ * Nat.gcdA g s₃
  let c := Nat.gcdB g s₃
  have hbez : (s₁ : ℤ) * a + (s₂ : ℤ) * b + (s₃ : ℤ) * c = 1 := by
    calc
      _ = ((s₁ : ℤ) * Nat.gcdA s₁ s₂ + (s₂ : ℤ) * Nat.gcdB s₁ s₂) *
          Nat.gcdA g s₃ + (s₃ : ℤ) * Nat.gcdB g s₃ := by dsimp [a, b, c]; ring
      _ = (g : ℤ) * Nat.gcdA g s₃ + (s₃ : ℤ) * Nat.gcdB g s₃ := by
        rw [← Nat.gcd_eq_gcd_ab s₁ s₂]
      _ = 1 := by rw [← Nat.gcd_eq_gcd_ab g s₃, show g.gcd s₃ = 1 from hprim]; rfl
  let t := a * (x₁ - y₁) + b * (x₂ - y₂) + c * (x₃ - y₃)
  refine ⟨t, ?_, ?_, ?_⟩ <;> dsimp only [t]
  · linear_combination -(x₁ - y₁) * hbez + b * h₁₂ + c * h₁₃
  · linear_combination -(x₂ - y₂) * hbez - a * h₁₂ + c * h₂₃
  · linear_combination -(x₃ - y₃) * hbez - a * h₁₃ - b * h₂₃

