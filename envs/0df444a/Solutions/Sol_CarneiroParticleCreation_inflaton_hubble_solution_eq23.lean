-- Prove2me | solution 1 for CarneiroParticleCreation.inflaton_hubble_solution_eq23
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:38:25.412145+00:00
-- url     : https://prove2.me/submissions/83d455e4-6031-4887-87ab-e64e93521068

import Mathlib

theorem solution (γ : ℝ) (Hφ V : ℝ → ℝ)
    (hd : Differentiable ℝ Hφ) (hpos : ∀ φ, 0 < Hφ φ)
    (h21 : ∀ φ, 3 * Hφ φ ^ 2 = V φ + 2 * deriv Hφ φ ^ 2)
    (hV : ∀ φ, V φ = 3 * γ * Hφ φ ^ 2 / 4)
    (I : Set ℝ) (hI : IsOpen I) (hIc : IsPreconnected I) (φ : ℝ → ℝ)
    (hφ : ∀ t ∈ I, DifferentiableAt ℝ φ t)
    (h22 : ∀ t ∈ I, deriv φ t = -2 * deriv Hφ (φ t)) :
    ∃ H₀ : ℝ, ∀ t ∈ I, 1 / Hφ (φ t) = 3 / 2 * ((4 - γ) / 2) * t + 1 / H₀ := by
  have hder : ∀ t ∈ I, HasDerivAt (fun s => (Hφ (φ s))⁻¹ - 3 / 2 * ((4 - γ) / 2) * s)
      (-(deriv Hφ (φ t) * deriv φ t) / Hφ (φ t) ^ 2 - 3 / 2 * ((4 - γ) / 2)) t := by
    intro t ht
    have h1 := ((hd (φ t)).hasDerivAt.comp t (hφ t ht).hasDerivAt).inv (hpos (φ t)).ne'
    have h2 := (hasDerivAt_id t).const_mul (3 / 2 * ((4 - γ) / 2))
    refine (h1.sub h2).congr_deriv ?_
    simp
  obtain ⟨c, hc⟩ := hI.exists_is_const_of_deriv_eq_zero hIc
    (f := fun s => (Hφ (φ s))⁻¹ - 3 / 2 * ((4 - γ) / 2) * s)
    (fun t ht => (hder t ht).differentiableAt.differentiableWithinAt)
    (by
      intro t ht
      rw [(hder t ht).deriv, h22 t ht]
      have e := h21 (φ t)
      rw [hV] at e
      have hp := (hpos (φ t)).ne'
      simp only [Pi.zero_apply]
      field_simp
      nlinarith [e])
  refine ⟨c⁻¹, fun t ht => ?_⟩
  have : (Hφ (φ t))⁻¹ - 3 / 2 * ((4 - γ) / 2) * t = c := hc t ht
  rw [one_div, one_div, inv_inv]
  linarith
