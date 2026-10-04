-- Prove2me | solution 1 for CouplingConstantRG.betaFunctionMu_eq_zero_scale_invariant
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T15:29:35.189737+00:00
-- url     : https://prove2.me/submissions/cb89cc3d-6e7e-41f3-85d7-988f5a67113e

import Mathlib
import Definitions.Def_CouplingConstantRGDefs

open CouplingConstantRG

theorem solution (g : ℝ → ℝ)
    (hg : ∀ μ, 0 < μ → DifferentiableAt ℝ g μ)
    (hβ : ∀ μ, 0 < μ → betaFunctionMu g μ = 0) :
    ∀ μ₁ μ₂ : ℝ, 0 < μ₁ → 0 < μ₂ → g μ₁ = g μ₂ := by
  intro μ₁ μ₂ h₁ h₂
  have hdiff : DifferentiableOn ℝ g (Set.Ioi 0) :=
    fun x hx => (hg x hx).differentiableWithinAt
  have hzero : (Set.Ioi (0 : ℝ)).EqOn (deriv g) 0 := by
    intro μ hμ
    have hβμ : μ * deriv g μ = 0 := by simpa [betaFunctionMu] using hβ μ hμ
    exact (mul_eq_zero.mp hβμ).resolve_left (ne_of_gt hμ)
  exact (isOpen_Ioi (a := (0 : ℝ))).is_const_of_deriv_eq_zero
    (convex_Ioi 0).isPreconnected hdiff hzero h₁ h₂
