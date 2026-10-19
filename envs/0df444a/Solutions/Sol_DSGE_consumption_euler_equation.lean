-- Prove2me | solution 1 for DSGE.consumption_euler_equation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:58:58.219548+00:00
-- url     : https://prove2.me/submissions/87236072-61c1-48e9-81a5-12632e2a1e77

import Mathlib

theorem solution (u : ℝ → ℝ) (β r w c₀ : ℝ)
    (hβ : 0 < β) (hr : 0 < 1 + r) (hc₀ : c₀ ∈ Set.Ioo 0 w)
    (hmax : ∀ c ∈ Set.Ioo 0 w,
      u c + β * u ((1 + r) * (w - c)) ≤ u c₀ + β * u ((1 + r) * (w - c₀)))
    (hu₀ : DifferentiableAt ℝ u c₀) (hu₁ : DifferentiableAt ℝ u ((1 + r) * (w - c₀))) :
    deriv u c₀ = β * (1 + r) * deriv u ((1 + r) * (w - c₀)) := by
  set g : ℝ → ℝ := fun c => u c + β * u ((1 + r) * (w - c)) with hg
  have hloc : IsLocalMax g c₀ :=
    Filter.eventually_of_mem (Ioo_mem_nhds hc₀.1 hc₀.2) fun c hc => hmax c hc
  have haff : HasDerivAt (fun c : ℝ => (1 + r) * (w - c)) (-(1 + r)) c₀ := by
    have := ((hasDerivAt_id' c₀).const_sub w).const_mul (1 + r)
    exact this.congr_deriv (by ring)
  have hder : HasDerivAt g (deriv u c₀ + β * (deriv u ((1 + r) * (w - c₀)) * (-(1 + r)))) c₀ :=
    hu₀.hasDerivAt.add ((hu₁.hasDerivAt.comp c₀ haff).const_mul β)
  have h0 := hloc.hasDerivAt_eq_zero hder
  linarith
