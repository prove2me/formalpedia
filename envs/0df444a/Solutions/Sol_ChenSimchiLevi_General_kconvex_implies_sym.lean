-- Prove2me | solution 1 for ChenSimchiLevi.General.kconvex_implies_sym
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:54:37.619532+00:00
-- url     : https://prove2.me/submissions/2901d987-a908-404d-8f02-b5acd399d44e

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_ChenSimchiLevi_General_SymKConvex

set_option autoImplicit false

theorem a4901261_key (K : ℝ) (g : ℝ → ℝ) (hf : BertsekasKConvex K g)
    (a c μ : ℝ) (hac : a < c) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) :
    g ((1 - μ) * a + μ * c) ≤ (1 - μ) * g a + μ * g c + μ * K := by
  have hca : 0 < c - a := sub_pos.2 hac
  have h := hf ((1 - μ) * (c - a)) (μ * (c - a)) ((1 - μ) * a + μ * c)
    (mul_nonneg (by linarith) hca.le) (mul_pos hμ0 hca)
  have e1 : (1 - μ) * a + μ * c - μ * (c - a) = a := by ring
  have e2 : (1 - μ) * (c - a) + ((1 - μ) * a + μ * c) = c := by ring
  have e3 : (1 - μ) * (c - a) / (μ * (c - a)) = (1 - μ) / μ :=
    mul_div_mul_right _ _ hca.ne'
  rw [e1, e2, e3] at h
  have hq : (1 - μ) / μ * μ = 1 - μ := div_mul_cancel₀ _ hμ0.ne'
  have h2 := mul_le_mul_of_nonneg_left h hμ0.le
  have e4 : μ * (g ((1 - μ) * a + μ * c) + (1 - μ) / μ * (g ((1 - μ) * a + μ * c) - g a))
      = g ((1 - μ) * a + μ * c) - (1 - μ) * g a := by
    rw [show μ * (g ((1 - μ) * a + μ * c) + (1 - μ) / μ * (g ((1 - μ) * a + μ * c) - g a))
        = μ * g ((1 - μ) * a + μ * c)
          + ((1 - μ) / μ * μ) * (g ((1 - μ) * a + μ * c) - g a) by ring, hq]
    ring
  rw [e4] at h2
  have e5 : μ * (K + g c) = μ * g c + μ * K := by ring
  rw [e5] at h2
  linarith

open ChenSimchiLevi.General in
theorem solution (k : ℝ) (f : ℝ → ℝ)
    (hf : BertsekasKConvex k f) : SymKConvex k f := by
  have hk : 0 ≤ k := by
    have := hf 0 1 0 le_rfl one_pos
    simp only [zero_div, zero_mul, add_zero, zero_add] at this
    linarith
  intro x₀ x₁ l hl
  obtain ⟨hl0, hl1⟩ := hl
  have hm1 : l * k ≤ max l (1 - l) * k := mul_le_mul_of_nonneg_right (le_max_left _ _) hk
  have hm2 : (1 - l) * k ≤ max l (1 - l) * k :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hk
  have hmk : 0 ≤ max l (1 - l) * k := mul_nonneg (le_trans hl0 (le_max_left _ _)) hk
  rcases lt_trichotomy x₀ x₁ with h | h | h
  · rcases eq_or_lt_of_le hl0 with h0 | h0
    · have e : (1 - l) * x₀ + l * x₁ = x₀ := by rw [← h0]; ring
      have e' : (1 - l) * f x₀ + l * f x₁ = f x₀ := by rw [← h0]; ring
      rw [e, e']
      linarith
    · have := a4901261_key k f hf x₀ x₁ l h h0 hl1
      linarith
  · subst h
    have e : (1 - l) * x₀ + l * x₀ = x₀ := by ring
    have e' : (1 - l) * f x₀ + l * f x₀ = f x₀ := by ring
    rw [e, e']
    linarith
  · rcases eq_or_lt_of_le hl1 with h1 | h1
    · have e : (1 - l) * x₀ + l * x₁ = x₁ := by rw [h1]; ring
      have e' : (1 - l) * f x₀ + l * f x₁ = f x₁ := by rw [h1]; ring
      rw [e, e']
      linarith
    · have := a4901261_key k f hf x₁ x₀ (1 - l) h (by linarith) (by linarith)
      have e : (1 - (1 - l)) * x₁ + (1 - l) * x₀ = (1 - l) * x₀ + l * x₁ := by ring
      have e' : (1 - (1 - l)) * f x₁ = l * f x₁ := by ring
      rw [e, e'] at this
      linarith
