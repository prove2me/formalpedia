-- Prove2me | solution 1 for BookProof.ChapterAttentionMarkov.push_isProb
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:04:43.295376+00:00
-- url     : https://prove2.me/submissions/0257167b-3708-47ff-b6f7-5e1694853246

-- Generated from ChapterAttentionMarkov.lean — solution of BookProof.ChapterAttentionMarkov.push_isProb
import Mathlib
import Definitions.Def_ChapterAttentionMarkov
import Theorems.Thm_BookProof_ChapterAttentionMarkov_push_nonneg
import Theorems.Thm_BookProof_ChapterAttentionMarkov_push_sum_one
open BookProof.ChapterAttentionMarkov



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {P : Fin m → Fin m → ℝ} {p : Fin m → ℝ} (hP : IsStochastic P)
    (hp : IsProb p) : IsProb (push P p) := ⟨fun j => push_nonneg hP hp.1 j, push_sum_one hP hp.2⟩
