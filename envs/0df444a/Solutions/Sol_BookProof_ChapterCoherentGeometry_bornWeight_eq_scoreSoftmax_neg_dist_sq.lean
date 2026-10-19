-- Prove2me | solution 1 for BookProof.ChapterCoherentGeometry.bornWeight_eq_scoreSoftmax_neg_dist_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:39:35.98348+00:00
-- url     : https://prove2.me/submissions/391c24f4-aae8-446a-aafe-d8ca1b9b243c

-- Generated from ChapterCoherentGeometry.lean — solution of BookProof.ChapterCoherentGeometry.bornWeight_eq_scoreSoftmax_neg_dist_sq
import Mathlib
import Definitions.Def_ChapterCoherentGeometry
import Theorems.Thm_BookProof_ChapterCoherentGeometry_bornNumer_eq_exp_neg_dist_sq
import Definitions.Def_ChapterCoherentOverlap
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterCoherentGeometry



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    bornWeight q k j = scoreSoftmax 1 (fun l => -‖q - k l‖ ^ 2) j := by
  rw [bornWeight, scoreSoftmax, bornNumer_eq_exp_neg_dist_sq]
  simp only [one_mul]
  exact congrArg _ (Finset.sum_congr rfl fun l _ => bornNumer_eq_exp_neg_dist_sq q (k l))

/-! ## The nearest key wins -/
