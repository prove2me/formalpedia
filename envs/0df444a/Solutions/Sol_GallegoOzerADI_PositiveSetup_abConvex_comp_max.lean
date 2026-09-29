-- Prove2me | solution 1 for GallegoOzerADI.PositiveSetup.abConvex_comp_max
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T00:10:15.75738+00:00
-- url     : https://prove2.me/submissions/b6a3bd9b-dbb2-45e2-84d9-9db01c847494

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex

open GallegoOzerADI.PositiveSetup

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a < b) (g : ℝ → ℝ)
    (hg : ABConvex a b g) (s : ℝ) (hs : ∀ x, s ≤ x → g s + a ≤ g x + b) :
    ABConvex a b (fun x => g (max x s)) := by
  intro x₁ x₂ hx θ hθ0 hθ1
  have hz1 : x₁ ≤ θ * x₁ + (1 - θ) * x₂ := by nlinarith
  have hz2 : θ * x₁ + (1 - θ) * x₂ ≤ x₂ := by nlinarith
  by_cases hs1 : s ≤ x₁
  · have e1 : max x₁ s = x₁ := max_eq_left hs1
    have e2 : max x₂ s = x₂ := max_eq_left (le_trans hs1 hx)
    have e3 : max (θ * x₁ + (1 - θ) * x₂) s = θ * x₁ + (1 - θ) * x₂ :=
      max_eq_left (le_trans hs1 hz1)
    simp only [e1, e2, e3]
    exact hg x₁ x₂ hx θ hθ0 hθ1
  · rw [not_le] at hs1
    by_cases hs2 : x₂ ≤ s
    · have e1 : max x₁ s = s := max_eq_right hs1.le
      have e2 : max x₂ s = s := max_eq_right hs2
      have e3 : max (θ * x₁ + (1 - θ) * x₂) s = s := max_eq_right (le_trans hz2 hs2)
      simp only [e1, e2, e3]
      nlinarith [ha, hb, hθ0, hθ1]
    · rw [not_le] at hs2
      have e1 : max x₁ s = s := max_eq_right hs1.le
      have e2 : max x₂ s = x₂ := max_eq_left hs2.le
      have hsx2 := hs x₂ hs2.le
      by_cases hzs : θ * x₁ + (1 - θ) * x₂ ≤ s
      · have e3 : max (θ * x₁ + (1 - θ) * x₂) s = s := max_eq_right hzs
        simp only [e1, e2, e3]
        nlinarith [hsx2, ha, hθ0, hθ1]
      · rw [not_le] at hzs
        have e3 : max (θ * x₁ + (1 - θ) * x₂) s = θ * x₁ + (1 - θ) * x₂ :=
          max_eq_left hzs.le
        simp only [e1, e2, e3]
        have hden : (0 : ℝ) < x₂ - s := by linarith
        have hne : x₂ - s ≠ 0 := ne_of_gt hden
        set μ : ℝ := (x₂ - (θ * x₁ + (1 - θ) * x₂)) / (x₂ - s) with hμ
        have hμ0 : 0 ≤ μ := by
          rw [hμ]
          apply div_nonneg _ hden.le
          linarith
        have hμ1 : μ ≤ 1 := by
          rw [hμ, div_le_one hden]
          linarith
        have hcomb : μ * s + (1 - μ) * x₂ = θ * x₁ + (1 - θ) * x₂ := by
          rw [hμ]
          field_simp
          ring
        have hgμ := hg s x₂ hs2.le μ hμ0 hμ1
        rw [hcomb] at hgμ
        have hμθ : θ ≤ μ := by
          rw [← sub_nonneg, hμ]
          have hexp : (x₂ - (θ * x₁ + (1 - θ) * x₂)) / (x₂ - s) - θ
              = ((x₂ - (θ * x₁ + (1 - θ) * x₂)) - θ * (x₂ - s)) / (x₂ - s) := by
            field_simp
          rw [hexp]
          apply div_nonneg _ hden.le
          nlinarith [mul_nonneg hθ0 (by linarith : (0 : ℝ) ≤ s - x₁)]
        nlinarith [hgμ, mul_nonneg (by linarith : (0 : ℝ) ≤ μ - θ)
          (by linarith : (0 : ℝ) ≤ (b + g x₂) - (a + g s))]
