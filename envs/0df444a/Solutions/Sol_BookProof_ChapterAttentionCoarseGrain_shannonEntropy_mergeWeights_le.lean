-- Prove2me | solution 1 for BookProof.ChapterAttentionCoarseGrain.shannonEntropy_mergeWeights_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:40:00.061637+00:00
-- url     : https://prove2.me/submissions/0a2d7e58-4ecf-4af4-ad6a-99fc8e35f347

-- Generated from ChapterAttentionCoarseGrain.lean — solution of BookProof.ChapterAttentionCoarseGrain.shannonEntropy_mergeWeights_le
import Mathlib
import Definitions.Def_ChapterAttentionCoarseGrain
import Theorems.Thm_BookProof_ChapterAttentionCoarseGrain_le_mergeWeights
import Theorems.Thm_BookProof_ChapterAttentionCoarseGrain_sum_mergeWeights_log
import Definitions.Def_ChapterAttentionEntropy
open BookProof.ChapterAttentionEntropy
open BookProof.ChapterAttentionCoarseGrain



open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {f : Fin m → Fin r} {p : Fin m → ℝ}
    (hp : ∀ x, 0 ≤ p x) :
    shannonEntropy (mergeWeights f p) ≤ shannonEntropy p := by

  have hterm : ∀ x : Fin m,
      p x * Real.log (p x) ≤ p x * Real.log (mergeWeights f p (f x)) := by
    intro x
    rcases eq_or_lt_of_le (hp x) with h | h
    · simp [← h]
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log h (le_mergeWeights hp x)) (hp x)
  have hsum : ∑ x, p x * Real.log (p x)
      ≤ ∑ x, p x * Real.log (mergeWeights f p (f x)) :=
    Finset.sum_le_sum fun x _ => hterm x
  rw [shannonEntropy, shannonEntropy, neg_le_neg_iff, sum_mergeWeights_log]
  exact hsum
