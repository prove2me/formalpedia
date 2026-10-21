-- Prove2me | solution 1 for ChenSimchiLevi.Additive.kconvex_def22_iff_def21
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:22:42.892692+00:00
-- url     : https://prove2.me/submissions/a3b4ca47-36a7-4ac3-a773-9b12161e10c5

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_ChenSimchiLevi_Additive_KConvexPorteus

set_option autoImplicit false

theorem solution (k : ℝ) (f : ℝ → ℝ) :
    ChenSimchiLevi.Additive.KConvexPorteus k f ↔ BertsekasKConvex k f := by
  constructor
  · intro h z b y hz hb
    have hzb : 0 < z + b := by linarith
    have hlam : (b / (z + b)) ∈ Set.Icc (0:ℝ) 1 := by
      constructor
      · positivity
      · rw [div_le_one hzb]; linarith
    have := h (y - b) (z + y) (b / (z + b)) (by linarith) hlam
    have hy : (1 - b / (z + b)) * (y - b) + b / (z + b) * (z + y) = y := by
      field_simp
      ring
    rw [hy] at this
    have h1 : (1 - b / (z + b)) = z / (z + b) := by field_simp; ring
    rw [h1] at this
    have h2 : f y * (z + b) ≤ z * f (y - b) + b * f (z + y) + b * k := by
      have := mul_le_mul_of_nonneg_right this hzb.le
      have e : (z / (z + b) * f (y - b) + b / (z + b) * f (z + y) + b / (z + b) * k) * (z + b)
          = z * f (y - b) + b * f (z + y) + b * k := by
        field_simp
      linarith
    have : f y + z / b * (f y - f (y - b)) = (f y * (z + b) - z * f (y - b)) / b := by
      field_simp
      ring
    rw [this, div_le_iff₀ hb]
    nlinarith
  · intro h x₀ x₁ lam hx hl
    obtain ⟨hl0, hl1⟩ := hl
    have hk : 0 ≤ k := by
      have := h 0 1 0 le_rfl one_pos
      linarith
    rcases hx.eq_or_lt with hx' | hx'
    · subst hx'
      have : (1 - lam) * x₀ + lam * x₀ = x₀ := by ring
      rw [this]
      nlinarith [mul_nonneg hl0 hk]
    rcases hl0.eq_or_lt with hl' | hl'
    · subst hl'
      simp
    set y := (1 - lam) * x₀ + lam * x₁ with hy
    set b := lam * (x₁ - x₀) with hb
    set z := (1 - lam) * (x₁ - x₀) with hz
    have hb0 : 0 < b := mul_pos hl' (by linarith)
    have hz0 : 0 ≤ z := mul_nonneg (by linarith) (by linarith)
    have e1 : y - b = x₀ := by rw [hy, hb]; ring
    have e2 : z + y = x₁ := by rw [hy, hz]; ring
    have := h z b y hz0 hb0
    rw [e1, e2] at this
    have hD : 0 < x₁ - x₀ := by linarith
    have h3 : (f y * b + z * f y - z * f x₀) ≤ b * k + b * f x₁ := by
      have := mul_le_mul_of_nonneg_left this hb0.le
      have e : b * (f y + z / b * (f y - f x₀)) = f y * b + z * f y - z * f x₀ := by
        field_simp
        ring
      nlinarith
    have hbz : b + z = x₁ - x₀ := by rw [hb, hz]; ring
    have h4 : f y * (x₁ - x₀) ≤ z * f x₀ + b * f x₁ + b * k := by nlinarith
    have hzD : z = (1 - lam) * (x₁ - x₀) := rfl
    have hbD : b = lam * (x₁ - x₀) := rfl
    rw [hzD, hbD] at h4
    have : (x₁ - x₀) * f y ≤ (x₁ - x₀) * ((1 - lam) * f x₀ + lam * f x₁ + lam * k) := by nlinarith
    exact le_of_mul_le_mul_left this hD
