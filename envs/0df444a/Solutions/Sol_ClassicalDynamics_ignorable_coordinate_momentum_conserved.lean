-- Prove2me | solution 1 for ClassicalDynamics.ignorable_coordinate_momentum_conserved
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T00:48:12.517884+00:00
-- url     : https://prove2.me/submissions/37e382be-0969-4c05-85bb-984e8abba41d

import Definitions.Def_ClassicalDynamics_core

open ClassicalDynamics

theorem solution {n : ℕ} (L : Lagrangian n)
    (hL : IsSmoothLagrangian L) (j : Fin n)
    (hcyc : ∀ (t : ℝ) (x v : Fin n → ℝ), dLdq L j t x v = 0)
    (q : ℝ → Fin n → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hmot : IsMotion L q) :
    IsConstantInTime (momentum L j q) := by
  have hd : ∀ t, HasDerivAt (momentum L j q) 0 t := fun t => by
    have := hmot j t
    rw [hcyc] at this
    exact this
  intro t₁ t₂
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t₁ t₂
