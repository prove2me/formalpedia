-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlapComplex.bornWeightC_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:30:27.714165+00:00
-- url     : https://prove2.me/submissions/55bbf459-ff7b-461e-9bc4-ecce873912bf

-- Generated from ChapterCoherentOverlapComplex.lean — solution of BookProof.ChapterCoherentOverlapComplex.bornWeightC_ofReal
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
import Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_bornNumerC_ofReal
open BookProof.ChapterCoherentOverlapComplex



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    bornWeightC (ofRealVec q) (fun l => ofRealVec (k l)) j
      = BookProof.ChapterSoftmaxBorn.bornWeight q k j := by

  rw [bornWeightC, BookProof.ChapterSoftmaxBorn.bornWeight, bornNumerC_ofReal]
  congr 1
  exact Finset.sum_congr rfl fun l _ => bornNumerC_ofReal q (k l)
