-- Prove2me | solution 1 for BookProof.ChapterAttentionMixing.pushIter_isProb
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:08:34.293947+00:00
-- url     : https://prove2.me/submissions/26da971f-d4b5-494a-bd12-4e9a625f8bc0

-- Generated from ChapterAttentionMixing.lean — solution of BookProof.ChapterAttentionMixing.pushIter_isProb
import Mathlib
import Definitions.Def_ChapterAttentionMixing
import Theorems.Thm_BookProof_ChapterAttentionMixing_pushIter_succ
import Theorems.Thm_BookProof_ChapterAttentionMarkov_push_isProb
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMarkov
open BookProof.ChapterAttentionMixing



open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {P : Fin m → Fin m → ℝ} {p : Fin m → ℝ} (hP : IsStochastic P)
    (hp : IsProb p) (n : ℕ) : IsProb (pushIter P n p) := by

  induction n with
  | zero => exact hp
  | succ n ih => rw [pushIter_succ]; exact push_isProb hP ih
