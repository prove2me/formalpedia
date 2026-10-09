-- Prove2me | solution 1 for BookProof.ChapterAttentionMixture.mixture_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:09:14.506868+00:00
-- url     : https://prove2.me/submissions/dca04d58-e143-4e3a-a007-d7597aeb52a6

-- Generated from ChapterAttentionMixture.lean — solution of BookProof.ChapterAttentionMixture.mixture_nonneg
import Mathlib
import Definitions.Def_ChapterAttentionMixture
open BookProof.ChapterAttentionMixture



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {w : Fin H → ℝ} {p : Fin H → Fin m → ℝ} (hw : ∀ h, 0 ≤ w h)
    (hp : ∀ h j, 0 ≤ p h j) (j : Fin m) : 0 ≤ mixture w p j := Finset.sum_nonneg fun h _ => mul_nonneg (hw h) (hp h j)
