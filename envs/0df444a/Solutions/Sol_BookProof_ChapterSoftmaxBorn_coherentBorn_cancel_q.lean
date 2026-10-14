-- Prove2me | solution 1 for BookProof.ChapterSoftmaxBorn.coherentBorn_cancel_q
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:19:23.877039+00:00
-- url     : https://prove2.me/submissions/e5f500dd-8e37-4bb9-9120-ace0949e8f43

-- Generated from ChapterSoftmaxBorn.lean — solution of BookProof.ChapterSoftmaxBorn.coherentBorn_cancel_q
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
import Theorems.Thm_BookProof_ChapterSoftmaxBorn_coherentBorn_sq_eq
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterSoftmaxBorn



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    bornWeight q k j =
      Real.exp (-‖k j‖ ^ 2) * Real.exp (2 * inner ℝ q (k j)) /
        ∑ l, Real.exp (-‖k l‖ ^ 2) * Real.exp (2 * inner ℝ q (k l)) := by

  have hc : (0 : ℝ) < Real.exp (-‖q‖ ^ 2) := Real.exp_pos _
  have hsum : ∑ l, bornNumer q (k l)
      = Real.exp (-‖q‖ ^ 2) *
        ∑ l, Real.exp (-‖k l‖ ^ 2) * Real.exp (2 * inner ℝ q (k l)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [coherentBorn_sq_eq]
    ring
  rw [bornWeight, hsum, coherentBorn_sq_eq]
  rw [mul_assoc, mul_div_mul_left _ _ (ne_of_gt hc)]
