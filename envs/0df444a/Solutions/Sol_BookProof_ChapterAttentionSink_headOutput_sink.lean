-- Prove2me | solution 1 for BookProof.ChapterAttentionSink.headOutput_sink
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:40:11.265417+00:00
-- url     : https://prove2.me/submissions/013ebcfa-00fd-4976-aaa6-b95d5ac3ade7

-- Generated from ChapterAttentionSink.lean — solution of BookProof.ChapterAttentionSink.headOutput_sink
import Mathlib
import Definitions.Def_ChapterAttentionSink
import Theorems.Thm_BookProof_ChapterAttentionSink_scoreSoftmax_sink_succ
import Theorems.Thm_BookProof_ChapterAttentionOutput_headOutput_eq_sum
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterAttentionOutput
open BookProof.ChapterAttentionSink



open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta s0 : ℝ) (s : Fin m → ℝ) (v0 : E) (v : Fin m → E) :
    headOutput beta (Fin.cons s0 s) (Fin.cons v0 v)
      = sinkWeight beta s0 s • v0 + (1 - sinkWeight beta s0 s) • headOutput beta s v := by

  rw [headOutput_eq_sum, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  congr 1
  calc ∑ j, scoreSoftmax beta (Fin.cons s0 s) j.succ • v j
      = ∑ j, ((1 - sinkWeight beta s0 s) * scoreSoftmax beta s j) • v j :=
        Finset.sum_congr rfl fun j _ => by rw [scoreSoftmax_sink_succ]
    _ = (1 - sinkWeight beta s0 s) • ∑ j, scoreSoftmax beta s j • v j := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [mul_smul]
    _ = (1 - sinkWeight beta s0 s) • headOutput beta s v := rfl
