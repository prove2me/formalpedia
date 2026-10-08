-- Prove2me | solution 1 for BoydADMM.Constrained.indicator_projection
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:13:17.752133+00:00
-- url     : https://prove2.me/submissions/62a4b1cc-7731-4775-9ed4-d3c82b90b320

import Definitions.Def_BoydADMM_Constrained_Geometry

open BoydADMM.Constrained

theorem solution {n : ℕ} (C : Set (Vec n))
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconvex : Convex ℝ C)
    (ρ : ℝ) (hρ : 0 < ρ) (v p : Vec n) (hp : p ∈ C) :
    (∀ w ∈ C, (ρ / 2) * ‖v - p‖ ^ 2 ≤ (ρ / 2) * ‖v - w‖ ^ 2) ↔
      RandomGradFree.Nonsmooth.IsMetricProjection C v p := by
  have hρ2 : 0 < ρ / 2 := by positivity
  constructor
  · intro h
    refine ⟨hp, ?_⟩
    intro w hw
    have hsq := le_of_mul_le_mul_left (h w hw) hρ2
    nlinarith [norm_nonneg (v - p), norm_nonneg (v - w)]
  · rintro ⟨_, h⟩ w hw
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hρ2)
    exact pow_le_pow_left₀ (norm_nonneg (v - p)) (h w hw) 2

#print axioms solution
