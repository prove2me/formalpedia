-- Prove2me | solution 1 for BookProof.ChapterAttentionMixture.mixture_isProb
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:28:38.422637+00:00
-- url     : https://prove2.me/submissions/ff54d258-934b-4681-a924-2b50c99bd278

-- Generated from ChapterAttentionMixture.lean — solution of BookProof.ChapterAttentionMixture.mixture_isProb
import Mathlib
import Definitions.Def_ChapterAttentionMixture
import Theorems.Thm_BookProof_ChapterAttentionMixture_mixture_nonneg
import Theorems.Thm_BookProof_ChapterAttentionMixture_mixture_sum_one
open BookProof.ChapterAttentionMixture



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {w : Fin H → ℝ} {p : Fin H → Fin m → ℝ} (hw0 : ∀ h, 0 ≤ w h)
    (hw : ∑ h, w h = 1) (hp0 : ∀ h j, 0 ≤ p h j) (hp : ∀ h, ∑ j, p h j = 1) :
    (∀ j, 0 ≤ mixture w p j) ∧ ∑ j, mixture w p j = 1 := ⟨fun j => mixture_nonneg hw0 hp0 j, mixture_sum_one hw hp⟩
