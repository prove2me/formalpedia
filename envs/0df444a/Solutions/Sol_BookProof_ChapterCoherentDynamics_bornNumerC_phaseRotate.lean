-- Prove2me | solution 1 for BookProof.ChapterCoherentDynamics.bornNumerC_phaseRotate
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:07:16.612094+00:00
-- url     : https://prove2.me/submissions/00121ee1-c402-411c-9d4c-9109186ebefd

-- Generated from ChapterCoherentDynamics.lean — solution of BookProof.ChapterCoherentDynamics.bornNumerC_phaseRotate
import Mathlib
import Definitions.Def_ChapterCoherentDynamics
import Theorems.Thm_BookProof_ChapterCoherentDynamics_coherentOverlapC_phaseRotate
open BookProof.ChapterCoherentDynamics



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterCoherentFidelity

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (theta : ℝ) (q k : EuclideanSpace ℂ (Fin n)) :
    bornNumerC (phaseRotate theta q) (phaseRotate theta k) = bornNumerC q k := by

  rw [bornNumerC, bornNumerC, coherentOverlapC_phaseRotate]
