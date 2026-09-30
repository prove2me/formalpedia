-- Prove2me | solution 1 for FriedmannEquations.first_friedmann_density_parameters
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:35:18.576309+00:00
-- url     : https://prove2.me/submissions/c0d7d5d4-c7a5-4f54-9ee1-6b08de801a69

import Definitions.Def_FriedmannEquations_Defs
set_option autoImplicit false
open FriedmannEquations

theorem solution (G Λ k ρR ρM : ℝ) (hG : 0 < G) (R ρ : ℝ → ℝ) (t t₀ : ℝ)
    (hR : R t ≠ 0) (hR₀ : R t₀ ≠ 0) (hH₀ : hubble R t₀ ≠ 0)
    (hρ : ∀ s, ρ s = ρR / (R s / R t₀) ^ 4 + ρM / (R s / R t₀) ^ 3)
    (h₁ : FirstFriedmannEq G Λ k R ρ t) (h₁₀ : FirstFriedmannEq G Λ k R ρ t₀) :
    let a := R t / R t₀
    let H₀ := hubble R t₀
    let ΩR := densityParameter G H₀ ρR
    let ΩM := densityParameter G H₀ ρM
    let ΩΛ := densityParameter G H₀ (Λ / (8 * Real.pi * G))
    let Ωk := 1 - (ΩR + ΩM + ΩΛ)
    hubble R t ^ 2 / H₀ ^ 2 =
      ΩR * a ^ (-4 : ℤ) + ΩM * a ^ (-3 : ℤ) + Ωk * a ^ (-2 : ℤ) + ΩΛ := by
  have hρ₀ : ρ t₀ = ρR + ρM := by simpa [hR₀] using hρ t₀
  have hk : k = (R t₀) ^ 2 * (8 * Real.pi * G * (ρR + ρM) / 3 + Λ / 3 - hubble R t₀ ^ 2) := by
    unfold FirstFriedmannEq at h₁₀
    rw [hρ₀] at h₁₀
    field_simp [hR₀] at h₁₀ ⊢
    nlinarith
  dsimp only
  unfold densityParameter criticalDensity
  change hubble R t ^ 2 = _ at h₁
  rw [h₁, hk, hρ t]
  simp only [zpow_neg, zpow_ofNat]
  field_simp [hG.ne', Real.pi_ne_zero, hR, hR₀, hH₀]
  <;> ring
