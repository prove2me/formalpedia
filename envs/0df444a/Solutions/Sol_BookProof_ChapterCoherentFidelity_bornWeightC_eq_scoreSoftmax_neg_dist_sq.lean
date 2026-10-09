-- Prove2me | solution 1 for BookProof.ChapterCoherentFidelity.bornWeightC_eq_scoreSoftmax_neg_dist_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:10:02.506724+00:00
-- url     : https://prove2.me/submissions/f1e4ca29-a45b-4332-a437-57c0649d338a

-- Generated from ChapterCoherentFidelity.lean — solution of BookProof.ChapterCoherentFidelity.bornWeightC_eq_scoreSoftmax_neg_dist_sq
import Mathlib
import Definitions.Def_ChapterCoherentFidelity
import Theorems.Thm_BookProof_ChapterCoherentFidelity_fidelityC_eq_bornNumerC
import Theorems.Thm_BookProof_ChapterCoherentFidelity_fidelityC_eq_exp_neg_dist_sq
open BookProof.ChapterCoherentFidelity



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) :
    bornWeightC q k j = scoreSoftmax 1 (fun l => -‖q - k l‖ ^ 2) j := by

  rw [bornWeightC, scoreSoftmax]
  simp only [one_mul]
  rw [← fidelityC_eq_bornNumerC, fidelityC_eq_exp_neg_dist_sq]
  refine congrArg _ (Finset.sum_congr rfl fun l _ => ?_)
  rw [← fidelityC_eq_bornNumerC, fidelityC_eq_exp_neg_dist_sq]
