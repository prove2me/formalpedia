-- Prove2me | solution 2 for BookProof.NavierStokesFlow.nsFlowUnitary_eq_matrixFlow_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T19:45:48.926252+00:00
-- url     : https://prove2.me/submissions/553527aa-5828-4ea5-8a0c-d7cb62974308

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
  -- The point-free form is not published (its stub is the same platform
  -- theorem); derive it from the published pointwise lemma instead.
  have h : nsFlowUnitary d = matrixFlow (Complex.I • nsHamiltonian d) :=
    funext (nsFlowUnitary_eq_matrixFlow d)
  rw [h]
  exact matrixFlow_hasDerivAt (Complex.I • nsHamiltonian d) t
