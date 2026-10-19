-- Prove2me | solution 1 for CarneiroParticleCreation.slow_roll_and_matter_fraction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:38:00.04239+00:00
-- url     : https://prove2.me/submissions/ebf1356e-0a21-4777-8b3e-09af3ea22bdb

import Mathlib

open Filter Topology

theorem solution (I : Set ℝ) (hI : IsOpen I)
    (γ : ℝ) (hγ : γ ≠ 4) (H ρm Λ : ℝ → ℝ)
    (hH : ∀ t ∈ I, DifferentiableAt ℝ H t)
    (h13 : ∀ t ∈ I, deriv ρm t + 3 * H t * (ρm t + ρm t / 3) = γ * H t * ρm t)
    (h14 : ∀ t ∈ I, ρm t + Λ t = 3 * H t ^ 2)
    (h16 : ∀ t ∈ I, Λ t = 3 * γ / 4 * H t ^ 2)
    (hH0 : ∀ t ∈ I, H t ≠ 0) :
    ∀ t ∈ I, - deriv H t / H t ^ 2 = (4 - γ) / 2 ∧
      ρm t / (3 * H t ^ 2) = ((4 - γ) / 2) / 2 := by
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
  have h4 : (4 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have key : 3 / 2 * (4 - γ) * H t * (deriv H t + (4 - γ) / 2 * H t ^ 2) = 0 := by
    linear_combination h
  have hH' : deriv H t = -((4 - γ) / 2 * H t ^ 2) := by
    rcases mul_eq_zero.mp key with h5 | h5
    · rcases mul_eq_zero.mp h5 with h6 | h6
      · exfalso; apply h4; linarith
      · exact absurd h6 h0
    · linarith
  constructor
  · rw [hH']; field_simp
  · rw [hρ]; field_simp; ring
