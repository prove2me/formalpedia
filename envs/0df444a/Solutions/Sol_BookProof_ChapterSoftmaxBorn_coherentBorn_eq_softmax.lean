-- Prove2me | solution 1 for BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:19:38.935456+00:00
-- url     : https://prove2.me/submissions/468aa681-7693-47f8-bd2f-b2816d03aa8d

-- Generated from ChapterSoftmaxBorn.lean — solution of BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
import Theorems.Thm_BookProof_ChapterSoftmaxBorn_coherentBorn_cancel_q
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterSoftmaxBorn



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m) :
    bornWeight q k j = softmax 2 q k j := by

  have hc : (0 : ℝ) < Real.exp (-r ^ 2) := Real.exp_pos _
  rw [coherentBorn_cancel_q, softmax]
  have hnum : Real.exp (-‖k j‖ ^ 2) * Real.exp (2 * inner ℝ q (k j))
      = Real.exp (-r ^ 2) * Real.exp (2 * inner ℝ q (k j)) := by rw [hk j]
  have hden : ∑ l, Real.exp (-‖k l‖ ^ 2) * Real.exp (2 * inner ℝ q (k l))
      = Real.exp (-r ^ 2) * ∑ l, Real.exp (2 * inner ℝ q (k l)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hk l]
  rw [hnum, hden, mul_div_mul_left _ _ (ne_of_gt hc)]
