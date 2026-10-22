-- Prove2me | solution 1 for AvramDividend.Classical.chat06_uniform_mark_exponential_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:19:51.610117+00:00
-- url     : https://prove2.me/submissions/9caec022-5742-4af5-b776-8cf1e7f61cd5

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory

namespace AvramChat06

/-- The unit-length Uniform(1,2) negative-claim mark has
a Laplace transform characterised by a product identity.
Unlike the quotient form, this identity remains valid at
θ=0 with no excluded parameter and follows directly from
the pinned substitution theorem. -/
theorem uniform_mark_exponential_integral_identity (θ : ℝ) :
    θ * (∫ x in (1 : ℝ)..2, Real.exp (-θ * x)) =
      Real.exp (-θ) - Real.exp (-(2 * θ)) := by
  have hsub := intervalIntegral.mul_integral_comp_mul_left
    (f := Real.exp) (c := -θ) (a := (1 : ℝ)) (b := (2 : ℝ))
  rw [integral_exp] at hsub
  have h1 : (-θ) * (1 : ℝ) = -θ := by ring
  have h2 : (-θ) * (2 : ℝ) = -(2 * θ) := by ring
  rw [h1, h2] at hsub
  nlinarith [hsub]

end AvramChat06

open AvramChat06

theorem solution (θ : ℝ) :
    θ * (∫ x in (1 : ℝ)..2, Real.exp (-θ * x)) =
      Real.exp (-θ) - Real.exp (-(2 * θ)) := by
  exact uniform_mark_exponential_integral_identity θ
