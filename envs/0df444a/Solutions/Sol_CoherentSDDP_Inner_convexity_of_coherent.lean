-- Prove2me | solution 1 for CoherentSDDP.Inner.convexity_of_coherent
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:32:03.075701+00:00
-- url     : https://prove2.me/submissions/6e0be1c2-ac84-4139-8c6a-f330c5d896be

import Mathlib
import Definitions.Def_CoherentSDDP_Inner_Basic

set_option autoImplicit false
open CoherentSDDP.Inner

theorem solution {Ω : Type*} (ρ : (Ω → ℝ) → ℝ) (hsub : RiskSubadditive ρ)
    (hhom : RiskPosHomogeneous ρ) :
    ∀ (Z₁ Z₂ : Ω → ℝ) (α : ℝ), 0 ≤ α → α ≤ 1 →
      ρ (α • Z₁ + (1 - α) • Z₂) ≤ α * ρ Z₁ + (1 - α) * ρ Z₂ := by
  intro Z₁ Z₂ α h0 h1
  rcases h0.eq_or_lt with rfl | hpos
  · simp
  rcases h1.eq_or_lt with rfl | hlt
  · simp
  calc ρ (α • Z₁ + (1 - α) • Z₂) ≤ ρ (α • Z₁) + ρ ((1 - α) • Z₂) := hsub _ _
    _ = α * ρ Z₁ + (1 - α) * ρ Z₂ := by
      rw [hhom α Z₁ hpos, hhom (1 - α) Z₂ (by linarith)]
