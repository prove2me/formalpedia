-- Prove2me | solution 1 for FlagshipMEA.Monopoly.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:42:44.84399+00:00
-- url     : https://prove2.me/submissions/502e33ab-29b3-4043-8ef1-1aa3f7fadaac

import Mathlib
set_option autoImplicit false

theorem solution (β₁ β₂ β₃ γ₁ γ₂ γ₃ m₁ m₂ : ℝ)
    (hβ : β₁ ≠ β₂ * β₃) (hγ : γ₁ ≠ γ₂ * γ₃)
    (hβdom : -β₃ < m₁) (hγdom : -γ₃ < m₁) (h12 : m₁ < m₂)
    (hval1 : (β₁ + β₂ * m₁) / (β₃ + m₁) =
      (γ₁ + γ₂ * m₁) / (γ₃ + m₁))
    (hval2 : (β₁ + β₂ * m₂) / (β₃ + m₂) =
      (γ₁ + γ₂ * m₂) / (γ₃ + m₂))
    (hslope : deriv (fun x : ℝ => (β₁ + β₂ * x) / (β₃ + x)) m₂ =
      deriv (fun x : ℝ => (γ₁ + γ₂ * x) / (γ₃ + x)) m₂) :
    β₁ = γ₁ ∧ β₂ = γ₂ ∧ β₃ = γ₃ := by
  have hu1 : 0 < β₃ + m₁ := by linarith
  have hu2 : 0 < β₃ + m₂ := by linarith
  have hv1 : 0 < γ₃ + m₁ := by linarith
  have hv2 : 0 < γ₃ + m₂ := by linarith
  have hd : ∀ (p1 p2 p3 : ℝ), 0 < p3 + m₂ →
      deriv (fun x : ℝ => (p1 + p2 * x) / (p3 + x)) m₂
        = (p2 * (p3 + m₂) - (p1 + p2 * m₂)) / (p3 + m₂) ^ 2 := by
    intro p1 p2 p3 h
    have := (((hasDerivAt_id' m₂).const_mul p2).const_add p1).div
      ((hasDerivAt_id' m₂).const_add p3) (ne_of_gt h)
    have h2 : HasDerivAt (fun x : ℝ => (p1 + p2 * x) / (p3 + x))
        ((p2 * 1 * (p3 + m₂) - (p1 + p2 * m₂) * 1) / (p3 + m₂) ^ 2) m₂ := this
    rw [h2.deriv]
    ring
  rw [hd β₁ β₂ β₃ hu2, hd γ₁ γ₂ γ₃ hv2] at hslope
  have E1 : (β₁ + β₂ * m₁) * (γ₃ + m₁) = (γ₁ + γ₂ * m₁) * (β₃ + m₁) := by
    rw [div_eq_div_iff hu1.ne' hv1.ne'] at hval1; exact hval1
  have E2 : (β₁ + β₂ * m₂) * (γ₃ + m₂) = (γ₁ + γ₂ * m₂) * (β₃ + m₂) := by
    rw [div_eq_div_iff hu2.ne' hv2.ne'] at hval2; exact hval2
  have E3 : (β₂ * (β₃ + m₂) - (β₁ + β₂ * m₂)) * (γ₃ + m₂) ^ 2
      = (γ₂ * (γ₃ + m₂) - (γ₁ + γ₂ * m₂)) * (β₃ + m₂) ^ 2 := by
    rw [div_eq_div_iff (by positivity) (by positivity)] at hslope; exact hslope
  -- notation
  set u := β₃ + m₂ with hu
  set v := γ₃ + m₂ with hv
  set A := β₂ - γ₂ with hA
  set a := β₁ - β₂ * β₃ with ha
  set c := γ₁ - γ₂ * γ₃ with hc
  have P2 : A * u * v + a * v - c * u = 0 := by
    simp only [hu, hv, hA, ha, hc]
    linear_combination E2
  have P3 : a * v ^ 2 = c * u ^ 2 := by
    simp only [hu, hv, ha, hc]
    linear_combination (-1 : ℝ) * E3
  have hder : A * (u + v) + a - c = 0 := by
    have h : (u * v) * (A * (u + v) + a - c) = 0 := by
      linear_combination (u + v) * P2 - P3
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (by positivity)
    · exact h
  -- P(m₁) = A (m₁ - m₂)^2
  have hA0 : A = 0 := by
    have h1 : A * (m₁ - m₂) ^ 2 = 0 := by
      simp only [hu, hv, hA, ha, hc] at hder P2 ⊢
      linear_combination E1 - E2 - (m₁ - m₂) * hder
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exfalso
      have : m₁ - m₂ = 0 := by simpa using h
      linarith
  have hac : a = c := by
    rw [hA0] at hder; linarith
  have hne : a ≠ 0 := by
    intro h; apply hβ; simp only [ha] at h; linarith
  have hb : β₃ = γ₃ := by
    have h1 : a * (γ₃ - β₃) = 0 := by
      have h2 := P2
      rw [hA0, ← hac] at h2
      have e : a * (γ₃ - β₃) = a * v - a * u := by
        simp only [hu, hv]; ring
      linarith
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hne
    · linarith
  refine ⟨?_, ?_, hb⟩
  · simp only [ha, hc] at hac
    have : β₂ = γ₂ := by simp only [hA] at hA0; linarith
    rw [← hb, ← this] at hac
    linarith
  · simp only [hA] at hA0; linarith
