-- Prove2me | solution 1 for BookProof.NavierStokesFlow.nsFlow_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T21:17:06.963491+00:00
-- url     : https://prove2.me/submissions/6c1a1a95-85ab-4b81-91c2-baa6949badee

import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
open BookProof.NavierStokesFlow
open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ} (d : NSTruncation n)

theorem solution (t : ℝ) :
    HasDerivAt (nsFlowUnitary d) (nsFlowUnitary d t * (Complex.I • nsHamiltonian d)) t := by
  let x : Matrix (Fin n) (Fin n) ℂ := Complex.I • nsHamiltonian d
  have h := hasDerivAt_exp_smul_const x t
  have hpt : ∀ u : ℝ, u • x = (((u : ℂ) * Complex.I) • nsHamiltonian d) := by
    intro u
    simp only [x]
    first | rw [Complex.real_smul] | rw [← smul_assoc, Complex.real_smul]
  have hfun : ∀ u, nsFlowUnitary d u = NormedSpace.exp (u • x) := by
    intro u
    simp only [nsFlowUnitary, hpt]
  have hderiv :
      NormedSpace.exp (t • x) * x = nsFlowUnitary d t * (Complex.I • nsHamiltonian d) := by
    rw [hfun]
  exact (h.congr_deriv hderiv).congr_of_eventuallyEq (Filter.Eventually.of_forall hfun)
