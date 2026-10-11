-- Prove2me | solution 1 for BookProof.ChapterAttentionOutput.tendsto_headOutput
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:45:15.109186+00:00
-- url     : https://prove2.me/submissions/4bdff36f-fb2c-4005-8ffc-e8cfe23408b7

-- Generated from ChapterAttentionOutput.lean — solution of BookProof.ChapterAttentionOutput.tendsto_headOutput
import Mathlib
import Definitions.Def_ChapterAttentionOutput
import Theorems.Thm_BookProof_ChapterSoftmaxSharpness_tendsto_scoreSoftmax_max
import Theorems.Thm_BookProof_ChapterSoftmaxSharpness_tendsto_scoreSoftmax_ne
import Theorems.Thm_BookProof_ChapterAttentionOutput_headOutput_eq_sum
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutput



open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (s : Fin m → ℝ) (v : Fin m → E) (j : Fin m)
    (hmax : ∀ l, l ≠ j → s l < s j) :
    Tendsto (fun b : ℝ => headOutput b s v) atTop (𝓝 (v j)) := by

  have h : Tendsto (fun b : ℝ => ∑ l, scoreSoftmax b s l • v l) atTop
      (𝓝 (∑ l : Fin m, (if l = j then (1 : ℝ) else 0) • v l)) := by
    refine tendsto_finset_sum _ fun l _ => ?_
    rcases eq_or_ne l j with hl | hl
    · subst hl
      simpa using (tendsto_scoreSoftmax_max s l hmax).smul_const (v l)
    · simpa [hl] using (tendsto_scoreSoftmax_ne s j l hmax hl).smul_const (v l)
  simpa [headOutput_eq_sum] using h
