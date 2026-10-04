-- Prove2me | solution 1 for CouplingConstantRG.betaFunctionMu_pos_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T15:27:47.700125+00:00
-- url     : https://prove2.me/submissions/a59271e6-f8a7-44ed-993c-ab59eb3ff47b

import Mathlib
import Definitions.Def_CouplingConstantRGDefs

open CouplingConstantRG

theorem solution (g : ℝ → ℝ)
    (hg : ∀ μ, 0 < μ → DifferentiableAt ℝ g μ)
    (hβ : ∀ μ, 0 < μ → 0 < betaFunctionMu g μ) :
    StrictMonoOn g (Set.Ioi 0) := by
  have hdiff : DifferentiableOn ℝ g (Set.Ioi 0) :=
    fun x hx => (hg x hx).differentiableWithinAt
  have hcont : ContinuousOn g (Set.Ioi 0) := hdiff.continuousOn
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) hcont ?_
  intro x hx
  rw [interior_Ioi] at hx
  have hβx : 0 < x * deriv g x := by simpa [betaFunctionMu] using hβ x hx
  exact (mul_pos_iff_of_pos_left hx).1 hβx
