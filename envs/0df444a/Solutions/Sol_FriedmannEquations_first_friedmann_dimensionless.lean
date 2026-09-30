-- Prove2me | solution 1 for FriedmannEquations.first_friedmann_dimensionless
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:35:17.956794+00:00
-- url     : https://prove2.me/submissions/c4505ee7-ed36-43eb-a168-f99757b8b4e1

import Definitions.Def_FriedmannEquations_Defs
set_option autoImplicit false
open FriedmannEquations

theorem vacuum_energy (G Λ k : ℝ) (hG : 0 < G) (R ρ p : ℝ → ℝ) (t : ℝ) :
    (FirstFriedmannEq G Λ k R (fun s => ρ s - Λ / (8 * Real.pi * G)) t ↔
      FirstFriedmannEq G 0 k R ρ t) ∧
    (SecondFriedmannEq G Λ R (fun s => ρ s - Λ / (8 * Real.pi * G))
        (fun s => p s + Λ / (8 * Real.pi * G)) t ↔
      SecondFriedmannEq G 0 R ρ p t) := by
  unfold FirstFriedmannEq SecondFriedmannEq
  constructor <;> constructor <;> intro hh
  all_goals field_simp [hG.ne', Real.pi_ne_zero] at hh ⊢
  all_goals simp only [div_eq_mul_inv] at hh ⊢
  all_goals nlinarith

theorem curvature_sign (G k : ℝ) (hG : 0 < G) (R ρ : ℝ → ℝ) (t : ℝ) (hR : R t ≠ 0)
    (h₁ : FirstFriedmannEq G 0 k R ρ t) :
    (k = 0 ↔ ρ t = criticalDensity G (hubble R t)) ∧
    (0 < k ↔ criticalDensity G (hubble R t) < ρ t) ∧
    (k < 0 ↔ ρ t < criticalDensity G (hubble R t)) := by
  let c : ℝ := 3 / (8 * Real.pi * G * R t ^ 2)
  have hc : 0 < c := by dsimp [c]; positivity
  have he : ρ t - criticalDensity G (hubble R t) = c * k := by
    unfold FirstFriedmannEq at h₁
    dsimp [criticalDensity, c]
    field_simp [hG.ne', Real.pi_ne_zero, hR] at *
    nlinarith
  constructor
  · symm
    rw [← sub_eq_zero, he, mul_eq_zero]
    simp [hc.ne']
  constructor
  · symm
    rw [← sub_pos, he, mul_pos_iff_of_pos_left hc]
  · symm
    rw [← sub_neg, he]
    constructor
    · intro hh
      by_contra hk
      exact (not_lt_of_ge (mul_nonneg hc.le (le_of_not_gt hk))) hh
    · intro hk
      exact mul_neg_of_pos_of_neg hc hk

theorem solution (G k : ℝ) (hG : 0 < G) (R ρ : ℝ → ℝ) (t t₀ : ℝ)
    (hR : R t ≠ 0) (hR₀ : R t₀ ≠ 0)
    (h₁ : FirstFriedmannEq G 0 k R ρ t) (h₁₀ : FirstFriedmannEq G 0 k R ρ t₀) :
    hubble (fun s => R s / R t₀) t = hubble R t ∧
    hubble (fun s => R s / R t₀) t ^ 2 =
      8 * Real.pi * G / 3 *
        (ρ t + (criticalDensity G (hubble R t₀) - ρ t₀) / (R t / R t₀) ^ 2) := by
  have hH : hubble (fun s => R s / R t₀) t = hubble R t := by
    unfold hubble
    rw [deriv_div_const]
    field_simp
  refine ⟨hH, ?_⟩
  rw [hH]
  unfold FirstFriedmannEq at h₁ h₁₀
  unfold criticalDensity
  field_simp [hG.ne', Real.pi_ne_zero, hR, hR₀] at *
  nlinarith
