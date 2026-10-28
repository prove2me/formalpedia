-- Prove2me | solution 1 for CompoundSMM.Conv.drop_proximal_term
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:20:27.401568+00:00
-- url     : https://prove2.me/submissions/15f69a56-7d01-4ec8-8564-3188db800ef1

import Mathlib
import Definitions.Def_CompoundSMM_Conv_Setting

open CompoundSMM.Conv in
theorem solution {n : ℕ} (X : Set (E n)) (hX : Convex ℝ X) (V : E n → ℝ)
    (hV : ConvexOn ℝ X V) (xinf : E n) (hxinf : xinf ∈ X) (ρ : ℝ) (hρ : 0 < ρ)
    (h15 : ∀ x ∈ X, V xinf ≤ V x + ‖x - xinf‖ ^ 2 / (2 * ρ)) :
    IsMinOn V X xinf := by
  rw [isMinOn_iff]
  intro x hx
  set D := ‖x - xinf‖ ^ 2 / (2 * ρ) with hD
  have hD0 : 0 ≤ D := by positivity
  have key : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → V xinf ≤ V x + θ * D := by
    intro θ hθ0 hθ1
    have hy : (1 - θ) • xinf + θ • x ∈ X := hX hxinf hx (by linarith) hθ0.le (by ring)
    have h1 := h15 _ hy
    have hdiff : (1 - θ) • xinf + θ • x - xinf = θ • (x - xinf) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hθ0, mul_pow] at h1
    have h2 := hV.2 hxinf hx (by linarith : (0:ℝ) ≤ 1 - θ) hθ0.le (by ring : (1 - θ) + θ = 1)
    simp only [smul_eq_mul] at h2
    have h3 : θ ^ 2 * ‖x - xinf‖ ^ 2 / (2 * ρ) = θ ^ 2 * D := by rw [hD]; ring
    rw [h3] at h1
    have h4 : θ * (V xinf - V x - θ * D) ≤ 0 := by nlinarith
    by_contra hc
    push_neg at hc
    have : 0 < θ * (V xinf - V x - θ * D) := mul_pos hθ0 (by linarith)
    linarith
  by_contra hc
  push_neg at hc
  set g := V xinf - V x with hg
  have hg0 : 0 < g := by linarith
  have hDg : 0 < D + g := by linarith
  have hθ1 : g / (D + g) ≤ 1 := by rw [div_le_one hDg]; linarith
  have h := key (g / (D + g)) (by positivity) hθ1
  have hlt : g / (D + g) * D < g := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hDg]; nlinarith
  linarith
