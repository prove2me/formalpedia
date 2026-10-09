-- Prove2me | solution 1 for BookProof.ChapterCoherentDynamics.bornNumerC_isometry
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:06:34.862598+00:00
-- url     : https://prove2.me/submissions/06807759-eba1-4696-87d6-01827bc0c19f

-- Generated from ChapterCoherentDynamics.lean — solution of BookProof.ChapterCoherentDynamics.bornNumerC_isometry
import Mathlib
import Definitions.Def_ChapterCoherentDynamics
import Theorems.Thm_BookProof_ChapterCoherentDynamics_coherentOverlapC_isometry
open BookProof.ChapterCoherentDynamics



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterCoherentFidelity

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (q k : EuclideanSpace ℂ (Fin n)) : bornNumerC (U q) (U k) = bornNumerC q k := by

  rw [bornNumerC, bornNumerC, coherentOverlapC_isometry]
