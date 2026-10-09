-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:29:59.513236+00:00
-- url     : https://prove2.me/submissions/7b5a8a7c-004b-432e-b71f-09bbabb6f622

-- Generated from ChapterCoherentOverlapComplex.lean — solution of BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
import Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_coherentBornC_cancel_q
open BookProof.ChapterCoherentOverlapComplex



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m) :
    bornWeightC q k j = softmaxC 2 q k j := by

  have hc : (0 : ℝ) < Real.exp (-r ^ 2) := Real.exp_pos _
  rw [coherentBornC_cancel_q, softmaxC]
  have hnum : Real.exp (-‖k j‖ ^ 2) * Real.exp (2 * (inner ℂ q (k j) : ℂ).re)
      = Real.exp (-r ^ 2) * Real.exp (2 * (inner ℂ q (k j) : ℂ).re) := by rw [hk j]
  have hden : ∑ l, Real.exp (-‖k l‖ ^ 2) * Real.exp (2 * (inner ℂ q (k l) : ℂ).re)
      = Real.exp (-r ^ 2) * ∑ l, Real.exp (2 * (inner ℂ q (k l) : ℂ).re) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hk l]
  rw [hnum, hden, mul_div_mul_left _ _ (ne_of_gt hc)]
