-- Prove2me | solution 1 for BookProof.NavierStokesFlow.derivativeField_momentum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:38:57.337077+00:00
-- url     : https://prove2.me/submissions/fce955bf-72cb-4319-838c-0f995fcc96fc

-- Generated from ChapterNavierStokesFlow.lean — solution of BookProof.NavierStokesFlow.derivativeField_momentum
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Theorems.Thm_BookProof_NavierStokesFlow_ccr_field
open BookProof.NavierStokesFlow



open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

set_option maxHeartbeats 1000000 in
theorem solution (j k m n : Fin 3) (p : MvPolynomial (Fin 3 × Fin 3) ℂ) :
    (MvPolynomial.pderiv (m, n)) (MvPolynomial.X (j, k) * p)
      - MvPolynomial.X (j, k) * (MvPolynomial.pderiv (m, n)) p
      = (if m = j ∧ n = k then p else 0) := by

  rw [ccr_field]
  simp [Prod.ext_iff]
