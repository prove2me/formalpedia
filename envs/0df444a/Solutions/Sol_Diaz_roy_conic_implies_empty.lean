-- Prove2me | solution 1 for Diaz.roy_conic_implies_empty
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:15:38.935197+00:00
-- url     : https://prove2.me/submissions/d6e62bc4-2b06-4174-806e-c66f58d2d0fc

import Mathlib

open ComplexConjugate

theorem solution {ρ : ℂ} (hρ : ρ ≠ 0) (L : Set ℂ)
    (hRoy : ∀ p : Fin 2 → ℂ, (∀ i, p i ∈ L) → p 0 * p 1 = ρ →
      ∃ V : Submodule ℚ (Fin 2 → ℂ), p ∈ V ∧ ∀ q ∈ V, q 0 * q 1 = ρ) :
    ∀ p : Fin 2 → ℂ, (∀ i, p i ∈ L) → p 0 * p 1 ≠ ρ := by
  intro p hp hcon
  obtain ⟨V, -, hV⟩ := hRoy p hp hcon
  have h0 := hV 0 V.zero_mem
  simp only [Pi.zero_apply, mul_zero] at h0
  exact hρ h0.symm
