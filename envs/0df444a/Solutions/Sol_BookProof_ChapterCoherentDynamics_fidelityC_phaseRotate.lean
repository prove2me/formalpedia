-- Prove2me | solution 1 for BookProof.ChapterCoherentDynamics.fidelityC_phaseRotate
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:07:17.714034+00:00
-- url     : https://prove2.me/submissions/72d64e8e-3288-491a-a294-fa05ad934c5f

-- Generated from ChapterCoherentDynamics.lean — solution of BookProof.ChapterCoherentDynamics.fidelityC_phaseRotate
import Mathlib
import Definitions.Def_ChapterCoherentDynamics
import Theorems.Thm_BookProof_ChapterCoherentDynamics_bornNumerC_phaseRotate
import Theorems.Thm_BookProof_ChapterCoherentFidelity_fidelityC_eq_bornNumerC
open BookProof.ChapterCoherentDynamics



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterCoherentFidelity

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (theta : ℝ) (q k : EuclideanSpace ℂ (Fin n)) :
    fidelityC (phaseRotate theta q) (phaseRotate theta k) = fidelityC q k := by

  rw [fidelityC_eq_bornNumerC, fidelityC_eq_bornNumerC, bornNumerC_phaseRotate]
