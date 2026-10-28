-- Prove2me | solution 1 for BoseGIE.gravitational_evolution_eq2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:22:44.096993+00:00
-- url     : https://prove2.me/submissions/6194edd4-5f36-4947-be25-6dda84f53684

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_BoseGIE_defs

open Matrix
open scoped Kronecker ComplexOrder
open BoseGIE

theorem solution (G m₁ m₂ hbar τ d Δx : ℝ) (hG : 0 < G) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hhbar : 0 < hbar) (hτ : 0 < τ) (hΔx : 0 < Δx) (hd : Δx < d) :
    let r : Qubit → Qubit → ℝ := ![![d, d + Δx], ![d - Δx, d]]
    let E : Qubit × Qubit → ℝ := fun p => -(G * m₁ * m₂) / r p.1 p.2
    let ψ₀ : Qubit × Qubit → ℂ := fun _ => 1 / 2
    let φ : ℝ := G * m₁ * m₂ * τ / (hbar * d)
    let φLR : ℝ := G * m₁ * m₂ * τ / (hbar * (d + Δx))
    let φRL : ℝ := G * m₁ * m₂ * τ / (hbar * (d - Δx))
    (fun p => Complex.exp (-((E p * τ / hbar : ℝ) : ℂ) * Complex.I) * ψ₀ p) =
        Complex.exp ((φ : ℂ) * Complex.I) • psiEnd (φLR - φ) (φRL - φ) ∧
      0 < (φLR - φ) + (φRL - φ) := by
  intro r E ψ₀ φ φLR φRL
  have hd0 : 0 < d := by linarith
  have h1 : 0 < d + Δx := by linarith
  have h2 : 0 < d - Δx := by linarith
  have hK : 0 < G * m₁ * m₂ * τ / hbar := by positivity
  refine ⟨?_, ?_⟩
  · have eE : ∀ x : ℝ, Complex.exp (x * Complex.I) =
        Complex.exp ((φ : ℂ) * Complex.I) * Complex.exp (((x - φ : ℝ) : ℂ) * Complex.I) := by
      intro x; rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e00 : E (0, 0) * τ / hbar = -φ := by
      simp only [E, r, φ]; simp; field_simp
    have e01 : E (0, 1) * τ / hbar = -φLR := by
      simp only [E, r, φLR]; simp; field_simp
    have e10 : E (1, 0) * τ / hbar = -φRL := by
      simp only [E, r, φRL]; simp; field_simp
    have e11 : E (1, 1) * τ / hbar = -φ := by
      simp only [E, r, φ]; simp; field_simp
    funext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j
    · show Complex.exp (-((E (0, 0) * τ / hbar : ℝ) : ℂ) * Complex.I) * (1 / 2) = _
      rw [e00]; simp [psiEnd]
    · show Complex.exp (-((E (0, 1) * τ / hbar : ℝ) : ℂ) * Complex.I) * (1 / 2) = _
      rw [e01]; simp only [Complex.ofReal_neg, neg_neg]; rw [eE φLR]; simp [psiEnd]; ring
    · show Complex.exp (-((E (1, 0) * τ / hbar : ℝ) : ℂ) * Complex.I) * (1 / 2) = _
      rw [e10]; simp only [Complex.ofReal_neg, neg_neg]; rw [eE φRL]; simp [psiEnd]; ring
    · show Complex.exp (-((E (1, 1) * τ / hbar : ℝ) : ℂ) * Complex.I) * (1 / 2) = _
      rw [e11]; simp [psiEnd]
  · have key : (φLR - φ) + (φRL - φ) =
        (G * m₁ * m₂ * τ / hbar) * (2 * Δx ^ 2 / (d * (d + Δx) * (d - Δx))) := by
      simp only [φ, φLR, φRL]
      field_simp
      ring
    rw [key]
    have : 0 < 2 * Δx ^ 2 / (d * (d + Δx) * (d - Δx)) := by positivity
    positivity
