-- Prove2me | solution 1 for BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:32:25.139898+00:00
-- url     : https://prove2.me/submissions/9ce80517-1382-4b01-84cb-02020c1df079

-- Generated from ChapterSoftmaxJacobian.lean — solution of BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxJacobian



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s x : Fin m → ℝ) :
    ∑ i, ∑ j, x i * softmaxJacobian beta s i j * x j = beta * weightedVar beta s x := by

  have key : ∀ i : Fin m, ∑ j, x i * softmaxJacobian beta s i j * x j
      = beta * (scoreSoftmax beta s i * x i ^ 2)
        - beta * (scoreSoftmax beta s i * x i) * ∑ j, scoreSoftmax beta s j * x j := by
    intro i
    have hterm : ∀ j : Fin m, x i * softmaxJacobian beta s i j * x j
        = (if j = i then beta * (scoreSoftmax beta s j * x j * x i) else 0)
          - beta * (scoreSoftmax beta s i * x i) * (scoreSoftmax beta s j * x j) := by
      intro j
      rcases eq_or_ne j i with hj | hj
      · subst hj
        rw [softmaxJacobian, if_pos (rfl : j = j), if_pos (rfl : j = j)]
        ring
      · rw [softmaxJacobian, if_neg hj, if_neg hj]
        ring
    have hpick : ∑ j, (if j = i then beta * (scoreSoftmax beta s j * x j * x i) else 0)
        = beta * (scoreSoftmax beta s i * x i ^ 2) := by
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      ring
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib, hpick,
      ← Finset.mul_sum]
  have expand : ∑ i, ∑ j, x i * softmaxJacobian beta s i j * x j
      = (∑ i, beta * (scoreSoftmax beta s i * x i ^ 2))
        - ∑ i, beta * (scoreSoftmax beta s i * x i) * ∑ j, scoreSoftmax beta s j * x j := by
    rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_sub_distrib]
  rw [expand, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, weightedVar]
  ring
