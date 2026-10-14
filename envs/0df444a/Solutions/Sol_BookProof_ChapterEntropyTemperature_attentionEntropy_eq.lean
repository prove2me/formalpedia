-- Prove2me | solution 1 for BookProof.ChapterEntropyTemperature.attentionEntropy_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T11:40:29.732079+00:00
-- url     : https://prove2.me/submissions/2d8acaf6-fcd4-4359-bf8e-79b1ba75079d

-- Generated from ChapterEntropyTemperature.lean — theorem BookProof.ChapterEntropyTemperature.attentionEntropy_eq
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterEntropyTemperature
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterEntropyTemperature


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}
open BookProof.ChapterEntropyTemperature

theorem solution(beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    attentionEntropy beta s = logPartition beta s - beta * meanScore beta s := by
  have hZ : 0 < ∑ l, Real.exp (beta * s l) := Finset.sum_pos (fun l _ => Real.exp_pos _) ⟨i, Finset.mem_univ _⟩
  have hsum : ∑ j, scoreSoftmax beta s j = 1 := by
    unfold scoreSoftmax
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  have hlog : ∀ j, Real.log (scoreSoftmax beta s j) = beta * s j - Real.log (∑ l, Real.exp (beta * s l)) := by
    intro j
    unfold scoreSoftmax
    rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  unfold attentionEntropy shannonEntropy logPartition partition meanScore
  simp_rw [hlog]
  rw [show ∑ j, scoreSoftmax beta s j * (beta * s j - Real.log (∑ l, Real.exp (beta * s l))) = beta * ∑ j, scoreSoftmax beta s j * s j - Real.log (∑ l, Real.exp (beta * s l)) * ∑ j, scoreSoftmax beta s j by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring, hsum]
  ring
