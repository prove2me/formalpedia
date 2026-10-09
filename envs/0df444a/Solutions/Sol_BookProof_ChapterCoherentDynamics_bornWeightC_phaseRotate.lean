-- Prove2me | solution 1 for BookProof.ChapterCoherentDynamics.bornWeightC_phaseRotate
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:07:31.046229+00:00
-- url     : https://prove2.me/submissions/32d5a545-1ec5-4f8d-8cdb-2f0883d167c2

-- Generated from ChapterCoherentDynamics.lean — solution of BookProof.ChapterCoherentDynamics.bornWeightC_phaseRotate
import Mathlib
import Definitions.Def_ChapterCoherentDynamics
import Theorems.Thm_BookProof_ChapterCoherentDynamics_bornNumerC_phaseRotate
open BookProof.ChapterCoherentDynamics



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterCoherentFidelity

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (theta : ℝ) (q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) :
    bornWeightC (phaseRotate theta q) (fun l => phaseRotate theta (k l)) j
      = bornWeightC q k j := by

  rw [bornWeightC, bornWeightC, bornNumerC_phaseRotate]
  congr 1
  exact Finset.sum_congr rfl fun l _ => bornNumerC_phaseRotate theta q (k l)
