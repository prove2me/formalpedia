-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_convolution_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:21:54.707222+00:00
-- url     : https://prove2.me/submissions/bc1a187e-10d6-4510-ab39-9274c63b5cc0

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    (V ρ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hVmono : Monotone V) (hVnonneg : ∀ y, 0 ≤ V y)
    (hVzero : ∀ y < 0, V y = 0)
    (hVsec : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ V v - V u)
    (hρI : Integrable ρ) (hρnorm : (∫ r, ρ r) = 1)
    (hρpos : 0 ≤ᵐ[volume] ρ)
    (hρsupport : ∀ᵐ r ∂volume, ρ r ≠ 0 →
      r ∈ Icc (δ / 3) (2 * (δ / 3)))
    (hI : ∀ y : ℝ, Integrable (fun r => ρ r * V (y - r))) :
    let g : ℝ → ℝ := fun y => ∫ r, ρ r * V (y - r)
    MonotoneOn g (Ici 0) ∧
    (∀ y : ℝ, 0 ≤ g y) ∧
    (∀ y : ℝ, y ≤ 0 → g y = 0) ∧
    (∀ y : ℝ, g y ≤ V y) := by 
  dsimp only
  let g : ℝ → ℝ := fun y => ∫ r, ρ r * V (y - r)
  have hmono : Monotone g := by
    intro a b hab
    apply integral_mono_ae (hI a) (hI b)
    filter_upwards [hρpos] with r hr
    exact mul_le_mul_of_nonneg_left (hVmono (by linarith : a - r ≤ b - r)) hr
  have hnonneg (y : ℝ) : 0 ≤ g y := by
    apply integral_nonneg_of_ae
    filter_upwards [hρpos] with r hr
    exact mul_nonneg hr (hVnonneg _)
  have hzero (y : ℝ) (hy : y ≤ 0) : g y = 0 := by
    change (∫ r, ρ r * V (y - r)) = 0
    calc
      _ = ∫ r : ℝ, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [hρsupport] with r hr
        by_cases hz : ρ r = 0
        · simp [hz]
        · rw [hVzero _ (by have := (hr hz).1; linarith), mul_zero]
      _ = 0 := by simp
  have hle (y : ℝ) : g y ≤ V y := by
    have hh : (∫ r, ρ r * V (y - r)) ≤ ∫ r, ρ r * V y := by
      apply integral_mono_ae (hI y) (hρI.mul_const (V y))
      filter_upwards [hρpos, hρsupport] with r hp hs
      by_cases hz : ρ r = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left
          (hVmono (by have := (hs hz).1; linarith : y - r ≤ y)) hp
    rw [integral_mul_const, hρnorm, one_mul] at hh
    exact hh
  exact ⟨hmono.monotoneOn (Ici 0), hnonneg, hzero, hle⟩
