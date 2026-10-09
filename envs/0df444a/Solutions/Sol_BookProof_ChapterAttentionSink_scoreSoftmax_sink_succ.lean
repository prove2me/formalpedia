-- Prove2me | solution 1 for BookProof.ChapterAttentionSink.scoreSoftmax_sink_succ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:39:51.195577+00:00
-- url     : https://prove2.me/submissions/7e457655-4680-4726-afb0-634f7ef89cb8

-- Generated from ChapterAttentionSink.lean — solution of BookProof.ChapterAttentionSink.scoreSoftmax_sink_succ
import Mathlib
import Definitions.Def_ChapterAttentionSink
import Theorems.Thm_BookProof_ChapterAttentionSink_sink_denom
import Theorems.Thm_BookProof_ChapterAttentionSink_one_sub_sinkWeight_eq
open BookProof.ChapterAttentionSink



open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta s0 : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta (Fin.cons s0 s) j.succ
      = (1 - sinkWeight beta s0 s) * scoreSoftmax beta s j := by

  have hZ : 0 < ∑ l, Real.exp (beta * s l) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨j, Finset.mem_univ j⟩
  rw [one_sub_sinkWeight_eq, scoreSoftmax, scoreSoftmax, sink_denom]
  rw [div_mul_div_comm]
  rw [Fin.cons_succ]
  rw [mul_comm (∑ l, Real.exp (beta * s l)) (Real.exp (beta * s j))]
  rw [mul_div_mul_right _ _ hZ.ne']
