-- Prove2me | solution 1 for BookProof.NavierStokesFlow.nsFlowUnitary_eq_matrixFlow_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T19:45:34.502496+00:00
-- url     : https://prove2.me/submissions/03f5f5a6-da62-48e2-8db8-b0d4cdd687a6

-- Generated from ChapterNavierStokesCauchy.lean — solution of BookProof.NavierStokesFlow.nsFlowUnitary_eq_matrixFlow'
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Theorems.Thm_BookProof_NavierStokesFlow_nsFlowUnitary_eq_matrixFlow
import Theorems.Thm_BookProof_NavierStokesFlow_matrixFlow_hasDerivAt
open BookProof.NavierStokesFlow



open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}
variable {n : ℕ} (d : NSTruncation n)

set_option maxHeartbeats 1000000 in

theorem solution (t : ℝ) :
    HasDerivAt (nsFlowUnitary d) (nsFlowUnitary d t * (Complex.I • nsHamiltonian d)) t := by
  -- The point-free `nsFlowUnitary_eq_matrixFlow'` of the source chapter is not
  -- published under that name; the published pointwise lemma gives it.
  have h : nsFlowUnitary d = matrixFlow (Complex.I • nsHamiltonian d) :=
    funext (nsFlowUnitary_eq_matrixFlow d)
  rw [h]
  exact matrixFlow_hasDerivAt (Complex.I • nsHamiltonian d) t
