-- Prove2me | solution 1 for BookProof.ChapterAttentionLocality.mem_window
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:43:13.36199+00:00
-- url     : https://prove2.me/submissions/c76b7ddc-58a9-48be-b90b-592f96656a37

-- Generated from ChapterAttentionLocality.lean — solution of BookProof.ChapterAttentionLocality.mem_window
import Mathlib
import Definitions.Def_ChapterAttentionLocality
open BookProof.ChapterAttentionLocality



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {d : Fin m → ℝ} {R : ℝ} {l : Fin m} : l ∈ window d R ↔ d l < R := by

  simp [window]
