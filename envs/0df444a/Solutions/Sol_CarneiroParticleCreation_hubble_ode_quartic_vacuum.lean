-- Prove2me | solution 1 for CarneiroParticleCreation.hubble_ode_quartic_vacuum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:35:27.353013+00:00
-- url     : https://prove2.me/submissions/b2f1d480-e59a-48cf-baf3-5a943c804585

import Mathlib

open Filter Topology

theorem solution (I : Set ℝ) (hI : IsOpen I) (H ρm Λ : ℝ → ℝ)
    (hH : ∀ t ∈ I, DifferentiableAt ℝ H t)
    (hΛ : ∀ t ∈ I, Λ t = 3 * H t ^ 4)
    (h2 : ∀ t ∈ I, deriv ρm t + 3 * H t * (ρm t + ρm t / 3) = - deriv Λ t)
    (h3 : ∀ t ∈ I, ρm t + Λ t = 3 * H t ^ 2)
    (hH0 : ∀ t ∈ I, H t ≠ 0) :
    ∀ t ∈ I, deriv H t + 2 * H t ^ 2 - 2 * H t ^ 4 = 0 := by
  intro t ht
  have hd := (hH t ht).hasDerivAt
  have eΛ : Λ =ᶠ[𝓝 t] fun s => 3 * H s ^ 4 := by
    filter_upwards [hI.mem_nhds ht] with s hs using hΛ s hs
  have eρ : ρm =ᶠ[𝓝 t] fun s => 3 * H s ^ 2 - 3 * H s ^ 4 := by
    filter_upwards [hI.mem_nhds ht] with s hs
    have := h3 s hs; rw [hΛ s hs] at this; linarith
  have dΛ : deriv Λ t = 3 * (4 * H t ^ 3 * deriv H t) := by
    rw [eΛ.deriv_eq]
    have := (hd.pow 4).const_mul 3
    refine this.deriv.trans ?_; push_cast; ring
  have dρ : deriv ρm t = 3 * (2 * H t * deriv H t) - 3 * (4 * H t ^ 3 * deriv H t) := by
    rw [eρ.deriv_eq]
    have := ((hd.pow 2).const_mul 3).sub ((hd.pow 4).const_mul 3)
    refine this.deriv.trans ?_; push_cast; ring
  have h := h2 t ht
  rw [dΛ, dρ, show ρm t = 3 * H t ^ 2 - 3 * H t ^ 4 from eρ.eq_of_nhds] at h
  have h6 : 6 * H t * (deriv H t + 2 * H t ^ 2 - 2 * H t ^ 4) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h6 with h7 | h7
  · exact absurd (by linarith : H t = 0) (hH0 t ht)
  · exact h7
