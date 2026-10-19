-- Prove2me | solution 1 for BookProof.NavierStokesFlow.nsFlow_comm_hamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T19:45:45.080994+00:00
-- url     : https://prove2.me/submissions/59665d72-e21c-4e53-a11d-6438652ecad9

-- Generated from ChapterNavierStokesCauchy.lean — solution of BookProof.NavierStokesFlow.nsFlow_comm_hamiltonian
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Theorems.Thm_BookProof_NavierStokesFlow_nsFlowUnitary_eq_matrixFlow
import Theorems.Thm_BookProof_NavierStokesFlow_matrixFlow_commute_of_commute
open BookProof.NavierStokesFlow










open scoped BigOperators Matrix Matrix.Norms.Operator




variable {n : ℕ}

















variable {n : ℕ} (d : NSTruncation n)

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) :
    nsFlowUnitary d t * nsHamiltonian d = nsHamiltonian d * nsFlowUnitary d t := by

  rw [nsFlowUnitary_eq_matrixFlow]
  -- The published stub `matrixFlow_commute_of_commute` carries the WRONG
  -- statement (it re-declares this very theorem, not the source's matrix-level
  -- `Commute (matrixFlow A t) B`), so inline the source's one-line proof.
  have hcomm : Commute (Complex.I • nsHamiltonian d) (nsHamiltonian d) := by
    simp [Commute, SemiconjBy]
  exact ((hcomm.smul_left t).exp_left).eq
