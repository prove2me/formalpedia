-- Prove2me | solution 2 for CountingLLL.ContractedWalk.cubic_fixed_point_unique
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-13T08:12:13.704619+00:00
-- url     : https://prove2.me/submissions/5cb30508-2b83-4f28-a890-be7c9af9cc69

import Mathlib

set_option autoImplicit false

theorem solution (θ z g h : ℝ) (ht0 : 0 ≤ θ) (ht : θ < 1 / 3)
    ( _hz0 : 0 ≤ z) (hz : z ≤ 1) (hg0 : 0 ≤ g) (hg : g ≤ 1) (hh0 : 0 ≤ h) (hh : h ≤ 1)
    (hgEq : g = 1 - θ + θ * z * g ^ 3) (hhEq : h = 1 - θ + θ * z * h ^ 3) : g = h := by
  by_contra hne
  have hdiff : g - h = θ * z * (g ^ 3 - h ^ 3) := by linear_combination hgEq - hhEq
  have hfac : g ^ 3 - h ^ 3 = (g - h) * (g ^ 2 + g * h + h ^ 2) := by ring
  rw [hfac] at hdiff
  have hne' : g - h ≠ 0 := sub_ne_zero.mpr hne
  have hdiv : 1 = θ * z * (g ^ 2 + g * h + h ^ 2) := by
    apply mul_left_cancel₀ hne'
    linarith
  have hsum_le : g ^ 2 + g * h + h ^ 2 ≤ (3 : ℝ) := by
    nlinarith [sq_nonneg (g - h), hg0, hg, hh0, hh]
  have hnn : 0 ≤ g ^ 2 + g * h + h ^ 2 := by
    nlinarith [sq_nonneg g, sq_nonneg h, mul_nonneg hg0 hh0]
  have hθz : θ * z ≤ θ := by nlinarith
  have hprod : θ * z * (g ^ 2 + g * h + h ^ 2) ≤ 3 * θ := by
    calc
      θ * z * (g ^ 2 + g * h + h ^ 2)
          ≤ θ * (g ^ 2 + g * h + h ^ 2) := by nlinarith
      _ ≤ θ * 3 := by nlinarith
      _ = 3 * θ := by ring
  have h3θ : 3 * θ < 1 := by
    have : θ < 1 / 3 := ht
    linarith
  have : (1 : ℝ) < 1 := by
    calc
      (1 : ℝ) = θ * z * (g ^ 2 + g * h + h ^ 2) := hdiv
      _ ≤ 3 * θ := hprod
      _ < 1 := h3θ
  exact absurd this (lt_irrefl _)
