-- Prove2me | solution 1 for CarneiroParticleCreation.early_time_vacuum_law_eq16
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:38:17.217756+00:00
-- url     : https://prove2.me/submissions/97233695-337a-43b1-8801-62aeb7012ac0

import Mathlib

open Filter Topology

theorem solution (I : Set ℝ) (hI : IsOpen I) (hIc : IsPreconnected I)
    (γ : ℝ) (hγ : γ ≠ 4) (H ρm Λ : ℝ → ℝ)
    (hH : ∀ t ∈ I, DifferentiableAt ℝ H t) (hρ : ∀ t ∈ I, DifferentiableAt ℝ ρm t)
    (h13 : ∀ t ∈ I, deriv ρm t + 3 * H t * (ρm t + ρm t / 3) = γ * H t * ρm t)
    (h14 : ∀ t ∈ I, ρm t + Λ t = 3 * H t ^ 2)
    (hH0 : ∀ t ∈ I, H t ≠ 0) :
    (∀ t ∈ I, deriv (fun s => ρm s + Λ s) t +
        3 * H t * ((ρm t + Λ t) + (ρm t / 3 - Λ t)) = 0) ↔
      ∃ Λ₀ : ℝ, ∀ t ∈ I, Λ t = 3 * γ / 4 * H t ^ 2 + Λ₀ := by
  have h4 : (4 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have hsum : ∀ t ∈ I, deriv (fun s => ρm s + Λ s) t = 6 * H t * deriv H t := by
    intro t ht
    have e : (fun s => ρm s + Λ s) =ᶠ[𝓝 t] fun s => 3 * H s ^ 2 := by
      filter_upwards [hI.mem_nhds ht] with s hs using h14 s hs
    rw [e.deriv_eq]
    have := ((hH t ht).hasDerivAt.pow 2).const_mul 3
    refine this.deriv.trans ?_; push_cast; ring
  have eΛ : ∀ t ∈ I, Λ =ᶠ[𝓝 t] fun s => 3 * H s ^ 2 - ρm s := by
    intro t ht
    filter_upwards [hI.mem_nhds ht] with s hs
    have := h14 s hs; linarith
  have hΛd : ∀ t ∈ I, HasDerivAt Λ (6 * H t * deriv H t - deriv ρm t) t := by
    intro t ht
    have := (((hH t ht).hasDerivAt.pow 2).const_mul 3).sub (hρ t ht).hasDerivAt
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (eΛ t ht)
    push_cast; ring
  constructor
  · intro hE
    have hρH : ∀ t ∈ I, ρm t = -(3 / 2) * deriv H t := by
      intro t ht
      have h := hE t ht
      rw [hsum t ht] at h
      have : 4 * H t * (ρm t + 3 / 2 * deriv H t) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd (by linarith : H t = 0) (hH0 t ht)
      · linarith
    obtain ⟨c, hc⟩ := hI.exists_is_const_of_deriv_eq_zero hIc
      (f := fun s => Λ s - 3 * γ / 4 * H s ^ 2)
      (fun t ht => ((hΛd t ht).differentiableAt.sub
        (((hH t ht).pow 2).const_mul _)).differentiableWithinAt)
      (by
        intro t ht
        have := (hΛd t ht).sub (((hH t ht).hasDerivAt.pow 2).const_mul (3 * γ / 4))
        refine this.deriv.trans ?_
        have h := h13 t ht
        rw [hρH t ht] at h
        have h2 : deriv ρm t = (γ - 4) * H t * (-(3 / 2) * deriv H t) := by linarith
        rw [h2]; simp only [Pi.zero_apply]; push_cast; ring)
    refine ⟨c, fun t ht => ?_⟩
    have : Λ t - 3 * γ / 4 * H t ^ 2 = c := hc t ht
    linarith
  · rintro ⟨Λ₀, hl⟩ t ht
    rw [hsum t ht]
    have eρ : ρm =ᶠ[𝓝 t] fun s => (3 - 3 * γ / 4) * H s ^ 2 - Λ₀ := by
      filter_upwards [hI.mem_nhds ht] with s hs
      have := h14 s hs; rw [hl s hs] at this; linarith
    have dρ : deriv ρm t = (3 - 3 * γ / 4) * (2 * H t * deriv H t) := by
      rw [eρ.deriv_eq]
      have := (((hH t ht).hasDerivAt.pow 2).const_mul (3 - 3 * γ / 4)).sub_const Λ₀
      refine this.deriv.trans ?_; push_cast; ring
    have h := h13 t ht
    rw [dρ] at h
    have : (4 - γ) * H t * (ρm t + 3 / 2 * deriv H t) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 h4
      · exact absurd h2 (hH0 t ht)
    · have : ρm t = -(3 / 2) * deriv H t := by linarith
      rw [show ρm t + Λ t + (ρm t / 3 - Λ t) = 4 / 3 * ρm t by ring, this]; ring
