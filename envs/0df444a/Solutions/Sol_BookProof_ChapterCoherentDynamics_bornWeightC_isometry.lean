-- Prove2me | solution 1 for BookProof.ChapterCoherentDynamics.bornWeightC_isometry
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:06:48.095741+00:00
-- url     : https://prove2.me/submissions/7539a1ac-251f-4ca1-b36b-913d5fbca9c0

-- Generated from ChapterCoherentDynamics.lean — solution of BookProof.ChapterCoherentDynamics.bornWeightC_isometry
import Mathlib
import Definitions.Def_ChapterCoherentDynamics
import Theorems.Thm_BookProof_ChapterCoherentDynamics_bornNumerC_isometry
open BookProof.ChapterCoherentDynamics



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterCoherentFidelity

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) :
    bornWeightC (U q) (fun l => U (k l)) j = bornWeightC q k j := by

  rw [bornWeightC, bornWeightC, bornNumerC_isometry]
  congr 1
  exact Finset.sum_congr rfl fun l _ => bornNumerC_isometry U q (k l)
