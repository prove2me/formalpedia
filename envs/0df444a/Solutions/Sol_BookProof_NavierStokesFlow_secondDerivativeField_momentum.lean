-- Prove2me | solution 1 for BookProof.NavierStokesFlow.secondDerivativeField_momentum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:38:58.199857+00:00
-- url     : https://prove2.me/submissions/e0d927b2-2ed7-4bef-a5f2-206d500483cb

-- Generated from ChapterNavierStokesFlow.lean — solution of BookProof.NavierStokesFlow.secondDerivativeField_momentum
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Theorems.Thm_BookProof_NavierStokesFlow_ccr_field
open BookProof.NavierStokesFlow



open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

set_option maxHeartbeats 1000000 in
theorem solution (i j k l m n : Fin 3)
    (p : MvPolynomial (Fin 3 × Fin 3 × Fin 3) ℂ) :
    (MvPolynomial.pderiv (l, m, n)) (MvPolynomial.X (i, j, k) * p)
      - MvPolynomial.X (i, j, k) * (MvPolynomial.pderiv (l, m, n)) p
      = (if l = i ∧ m = j ∧ n = k then p else 0) := by

  rw [ccr_field]
  simp [Prod.ext_iff]
