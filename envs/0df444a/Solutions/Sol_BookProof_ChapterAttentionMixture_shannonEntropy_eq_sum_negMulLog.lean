-- Prove2me | solution 1 for BookProof.ChapterAttentionMixture.shannonEntropy_eq_sum_negMulLog
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:28:40.52966+00:00
-- url     : https://prove2.me/submissions/463935f1-da31-4420-8762-f59e5c9899a9

-- Generated from ChapterAttentionMixture.lean — solution of BookProof.ChapterAttentionMixture.shannonEntropy_eq_sum_negMulLog
import Mathlib
import Definitions.Def_ChapterAttentionMixture
import Definitions.Def_ChapterAttentionEntropy
open BookProof.ChapterAttentionEntropy
open BookProof.ChapterAttentionMixture



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin m → ℝ) :
    shannonEntropy p = ∑ j, Real.negMulLog (p j) := by

  rw [shannonEntropy, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Real.negMulLog]; ring
