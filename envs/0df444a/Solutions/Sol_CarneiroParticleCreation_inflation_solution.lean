-- Prove2me | solution 1 for CarneiroParticleCreation.inflation_solution
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:40:55.703573+00:00
-- url     : https://prove2.me/submissions/94b20d76-ab3c-48b6-8f2c-faeba85c58fa

import Mathlib

open Filter Topology

theorem solution (I : Set ℝ) (hI : IsOpen I) (hIc : IsPreconnected I)
    (γ : ℝ) (hγ : γ ≠ 4) (H ρm Λ : ℝ → ℝ)
    (hH : ∀ t ∈ I, DifferentiableAt ℝ H t)
    (h13 : ∀ t ∈ I, deriv ρm t + 3 * H t * (ρm t + ρm t / 3) = γ * H t * ρm t)
    (h14 : ∀ t ∈ I, ρm t + Λ t = 3 * H t ^ 2)
    (h16 : ∀ t ∈ I, Λ t = 3 * γ / 4 * H t ^ 2)
    (hH0 : ∀ t ∈ I, H t ≠ 0) :
    ∃ H₀ : ℝ, ∀ t ∈ I, 1 / H t = (4 - γ) / 2 * t + 1 / H₀ := by
  have h4 : (4 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have hH' : ∀ t ∈ I, deriv H t = -((4 - γ) / 2 * H t ^ 2) := by
    intro t ht
    have hd := (hH t ht).hasDerivAt
    have h0 := hH0 t ht
    have eρ : ρm =ᶠ[𝓝 t] fun s => (3 - 3 * γ / 4) * H s ^ 2 := by
      filter_upwards [hI.mem_nhds ht] with s hs
      have := h14 s hs; rw [h16 s hs] at this; linarith
    have dρ : deriv ρm t = (3 - 3 * γ / 4) * (2 * H t * deriv H t) := by
      rw [eρ.deriv_eq]
      have := (hd.pow 2).const_mul (3 - 3 * γ / 4)
      refine this.deriv.trans ?_; push_cast; ring
    have hρ : ρm t = (3 - 3 * γ / 4) * H t ^ 2 := eρ.eq_of_nhds
    have h := h13 t ht
    rw [dρ, hρ] at h
    have key : 3 / 2 * (4 - γ) * H t * (deriv H t + (4 - γ) / 2 * H t ^ 2) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp key with h5 | h5
    · rcases mul_eq_zero.mp h5 with h6 | h6
      · exfalso; apply h4; linarith
      · exact absurd h6 h0
    · linarith
  have hder : ∀ t ∈ I, HasDerivAt (fun s => (H s)⁻¹ - (4 - γ) / 2 * s) 0 t := by
    intro t ht
    have h1 := (hH t ht).hasDerivAt.inv (hH0 t ht)
    have h2 := (hasDerivAt_id t).const_mul ((4 - γ) / 2)
    refine (h1.sub h2).congr_deriv ?_
    rw [hH' t ht]
    have := hH0 t ht
    field_simp
    simp
  obtain ⟨c, hc⟩ := hI.exists_is_const_of_deriv_eq_zero hIc
    (f := fun s => (H s)⁻¹ - (4 - γ) / 2 * s)
    (fun t ht => (hder t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hder t ht).deriv)
  refine ⟨c⁻¹, fun t ht => ?_⟩
  have : (H t)⁻¹ - (4 - γ) / 2 * t = c := hc t ht
  rw [one_div, one_div, inv_inv]
  linarith
