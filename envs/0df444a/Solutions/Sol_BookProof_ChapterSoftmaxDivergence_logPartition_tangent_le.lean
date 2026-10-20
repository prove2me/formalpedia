-- Prove2me | solution 1 for BookProof.ChapterSoftmaxDivergence.logPartition_tangent_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:01:49.754978+00:00
-- url     : https://prove2.me/submissions/662506c7-1c7b-4f3f-9e16-47d7bf7fc796

-- Generated from ChapterSoftmaxDivergence.lean — theorem BookProof.ChapterSoftmaxDivergence.logPartition_tangent_le
import Definitions.Def_ChapterAttentionEntropy
import Mathlib
import Definitions.Def_ChapterSoftmaxDivergence
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxDivergence


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

theorem sm_partition_pos {m : ℕ} (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    0 < BookProof.ChapterSoftmaxFluctuation.partition beta s := by
  unfold BookProof.ChapterSoftmaxFluctuation.partition
  exact Finset.sum_pos (fun l _ => Real.exp_pos _) ⟨i, Finset.mem_univ _⟩

theorem sm_soft_eq {m : ℕ} (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    BookProof.ChapterSoftmaxSharpness.scoreSoftmax beta s j =
      Real.exp (beta * s j) / BookProof.ChapterSoftmaxFluctuation.partition beta s := rfl

theorem sm_soft_pos {m : ℕ} (beta : ℝ) (s : Fin m → ℝ) (i j : Fin m) :
    0 < BookProof.ChapterSoftmaxSharpness.scoreSoftmax beta s j := by
  rw [sm_soft_eq]; exact div_pos (Real.exp_pos _) (sm_partition_pos beta s i)

theorem sm_soft_sum {m : ℕ} (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    ∑ j, BookProof.ChapterSoftmaxSharpness.scoreSoftmax beta s j = 1 := by
  simp_rw [sm_soft_eq]
  rw [← Finset.sum_div]
  exact div_self (sm_partition_pos beta s i).ne'

theorem sm_kl {m : ℕ} (beta gamma : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    BookProof.ChapterSoftmaxDivergence.klDiv (BookProof.ChapterSoftmaxSharpness.scoreSoftmax beta s)
        (BookProof.ChapterSoftmaxSharpness.scoreSoftmax gamma s)
      = BookProof.ChapterSoftmaxFluctuation.logPartition gamma s
          - BookProof.ChapterSoftmaxFluctuation.logPartition beta s
          - (gamma - beta) * BookProof.ChapterSoftmaxFluctuation.meanScore beta s := by
  have hb := sm_partition_pos beta s i
  have hg := sm_partition_pos gamma s i
  have hlog : ∀ j, Real.log (BookProof.ChapterSoftmaxSharpness.scoreSoftmax beta s j /
      BookProof.ChapterSoftmaxSharpness.scoreSoftmax gamma s j) =
      (beta - gamma) * s j - BookProof.ChapterSoftmaxFluctuation.logPartition beta s
        + BookProof.ChapterSoftmaxFluctuation.logPartition gamma s := by
    intro j
    rw [sm_soft_eq, sm_soft_eq, div_div_div_eq, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) hg.ne', Real.log_mul hb.ne' (by positivity),
      Real.log_exp, Real.log_exp]
    unfold BookProof.ChapterSoftmaxFluctuation.logPartition
    ring
  unfold BookProof.ChapterSoftmaxDivergence.klDiv
  simp_rw [hlog]
  have hsum := sm_soft_sum beta s i
  unfold BookProof.ChapterSoftmaxFluctuation.meanScore
  simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
  rw [Finset.mul_sum]
  have : ∑ x, BookProof.ChapterSoftmaxSharpness.scoreSoftmax beta s x * ((beta - gamma) * s x) =
      ∑ x, (gamma - beta) * (BookProof.ChapterSoftmaxSharpness.scoreSoftmax beta s x * s x) * (-1) := by
    apply Finset.sum_congr rfl; intro x _; ring
  rw [this, ← Finset.sum_mul]
  ring

variable {m : ℕ}
theorem solution (beta gamma : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    logPartition beta s + (gamma - beta) * meanScore beta s ≤ logPartition gamma s := by
  have hkl := sm_kl beta gamma s i
  have hnn : 0 ≤ klDiv (scoreSoftmax beta s) (scoreSoftmax gamma s) := by
    unfold klDiv
    have : ∑ j, (scoreSoftmax beta s j - scoreSoftmax gamma s j) ≤
        ∑ j, scoreSoftmax beta s j * Real.log (scoreSoftmax beta s j / scoreSoftmax gamma s j) := by
      apply Finset.sum_le_sum
      intro j _
      have hp := sm_soft_pos beta s i j
      have hq := sm_soft_pos gamma s i j
      have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hp hq)
      rw [inv_div] at h1
      have : scoreSoftmax beta s j * (1 - scoreSoftmax gamma s j / scoreSoftmax beta s j) =
          scoreSoftmax beta s j - scoreSoftmax gamma s j := by field_simp
      rw [← this]
      exact mul_le_mul_of_nonneg_left h1 hp.le
    rw [Finset.sum_sub_distrib, sm_soft_sum beta s i, sm_soft_sum gamma s i, sub_self] at this
    exact this
  linarith
