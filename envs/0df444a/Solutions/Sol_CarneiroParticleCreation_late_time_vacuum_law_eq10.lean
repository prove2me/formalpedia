-- Prove2me | solution 1 for CarneiroParticleCreation.late_time_vacuum_law_eq10
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:38:07.958002+00:00
-- url     : https://prove2.me/submissions/f096c9e4-0c15-42f1-8d44-ef9fe736defa

import Mathlib

open Filter Topology

theorem solution (I : Set ℝ) (hI : IsOpen I) (hIc : IsPreconnected I)
    (Γ : ℝ) (H ρm Λ : ℝ → ℝ)
    (hH : ∀ t ∈ I, DifferentiableAt ℝ H t) (hρ : ∀ t ∈ I, DifferentiableAt ℝ ρm t)
    (h7 : ∀ t ∈ I, deriv ρm t + 3 * H t * ρm t = Γ * ρm t)
    (h8 : ∀ t ∈ I, ρm t + Λ t = 3 * H t ^ 2)
    (hH0 : ∀ t ∈ I, H t ≠ 0) (hΓ : ∀ t ∈ I, 3 * H t ≠ Γ) :
    (∀ t ∈ I, deriv (fun s => ρm s + Λ s) t + 3 * H t * ((ρm t + Λ t) + (- Λ t)) = 0) ↔
      ∃ lam₀ : ℝ, ∀ t ∈ I, Λ t = 2 * Γ * H t + lam₀ := by
  -- derivative of ρm + Λ = 3 H²
  have hsum : ∀ t ∈ I, deriv (fun s => ρm s + Λ s) t = 6 * H t * deriv H t := by
    intro t ht
    have e : (fun s => ρm s + Λ s) =ᶠ[𝓝 t] fun s => 3 * H s ^ 2 := by
      filter_upwards [hI.mem_nhds ht] with s hs using h8 s hs
    rw [e.deriv_eq]
    have := ((hH t ht).hasDerivAt.pow 2).const_mul 3
    refine this.deriv.trans ?_; push_cast; ring
  have eΛ : ∀ t ∈ I, Λ =ᶠ[𝓝 t] fun s => 3 * H s ^ 2 - ρm s := by
    intro t ht
    filter_upwards [hI.mem_nhds ht] with s hs
    have := h8 s hs; linarith
  have hΛd : ∀ t ∈ I, HasDerivAt Λ (6 * H t * deriv H t - deriv ρm t) t := by
    intro t ht
    have := (((hH t ht).hasDerivAt.pow 2).const_mul 3).sub (hρ t ht).hasDerivAt
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (eΛ t ht)
    push_cast; ring
  constructor
  · intro hE
    -- ρm = -2 H' on I
    have hρH : ∀ t ∈ I, ρm t = -2 * deriv H t := by
      intro t ht
      have h := hE t ht
      rw [hsum t ht] at h
      have : 3 * H t * (ρm t + 2 * deriv H t) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd (by linarith : H t = 0) (hH0 t ht)
      · linarith
    -- H' differentiable with H'' = (Γ - 3H) H'
    have hH2 : ∀ t ∈ I, HasDerivAt (deriv H) (-(deriv ρm t) / 2) t := by
      intro t ht
      have e : deriv H =ᶠ[𝓝 t] fun s => -(ρm s) / 2 := by
        filter_upwards [hI.mem_nhds ht] with s hs
        rw [hρH s hs]; ring
      exact ((hρ t ht).hasDerivAt.neg.div_const 2).congr_of_eventuallyEq e
    obtain ⟨c, hc⟩ := hI.exists_is_const_of_deriv_eq_zero hIc
      (f := fun s => Λ s - 2 * Γ * H s)
      (fun t ht => ((hΛd t ht).differentiableAt.sub
        ((hH t ht).const_mul _)).differentiableWithinAt)
      (by
        intro t ht
        have := (hΛd t ht).sub ((hH t ht).hasDerivAt.const_mul (2 * Γ))
        refine this.deriv.trans ?_
        have h := h7 t ht
        rw [hρH t ht] at h
        have h2 : deriv ρm t = (Γ - 3 * H t) * (-2 * deriv H t) := by linarith
        rw [h2]; simp only [Pi.zero_apply]; ring)
    refine ⟨c, fun t ht => ?_⟩
    have : Λ t - 2 * Γ * H t = c := hc t ht
    linarith
  · rintro ⟨lam₀, hl⟩ t ht
    rw [hsum t ht]
    have eρ : ρm =ᶠ[𝓝 t] fun s => 3 * H s ^ 2 - 2 * Γ * H s - lam₀ := by
      filter_upwards [hI.mem_nhds ht] with s hs
      have := h8 s hs; rw [hl s hs] at this; linarith
    have dρ : deriv ρm t = 6 * H t * deriv H t - 2 * Γ * deriv H t := by
      rw [eρ.deriv_eq]
      have := ((((hH t ht).hasDerivAt.pow 2).const_mul 3).sub
        ((hH t ht).hasDerivAt.const_mul (2 * Γ))).sub_const lam₀
      refine this.deriv.trans ?_; push_cast; ring
    have h := h7 t ht
    rw [dρ] at h
    have : (3 * H t - Γ) * (ρm t + 2 * deriv H t) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd (by linarith : 3 * H t = Γ) (hΓ t ht)
    · have : ρm t = -2 * deriv H t := by linarith
      rw [show ρm t + Λ t + -Λ t = ρm t by ring, this]; ring
