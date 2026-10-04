-- Prove2me | solution 1 for CouplingConstantRG.betaFunctionMu_neg_strictAntiOn
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T15:28:46.359437+00:00
-- url     : https://prove2.me/submissions/5e241900-0f0e-475a-ba05-6bf2dbab2a5d

import Mathlib
import Definitions.Def_CouplingConstantRGDefs

open CouplingConstantRG

theorem solution (g : ℝ → ℝ)
    (hg : ∀ μ, 0 < μ → DifferentiableAt ℝ g μ)
    (hβ : ∀ μ, 0 < μ → betaFunctionMu g μ < 0) :
    StrictAntiOn g (Set.Ioi 0) := by
  have hdiff : DifferentiableOn ℝ g (Set.Ioi 0) :=
    fun x hx => (hg x hx).differentiableWithinAt
  have hcont : ContinuousOn g (Set.Ioi 0) := hdiff.continuousOn
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) hcont ?_
  intro x hx
  rw [interior_Ioi] at hx
  have hβx : x * deriv g x < 0 := by simpa [betaFunctionMu] using hβ x hx
  exact neg_of_mul_neg_right (by simpa [mul_comm] using hβx) hx.le
