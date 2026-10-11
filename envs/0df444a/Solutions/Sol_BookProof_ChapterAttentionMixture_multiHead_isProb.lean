-- Prove2me | solution 1 for BookProof.ChapterAttentionMixture.multiHead_isProb
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:45:11.567224+00:00
-- url     : https://prove2.me/submissions/385d8897-9c66-49c0-bb0e-9305175dd419

-- Generated from ChapterAttentionMixture.lean — solution of BookProof.ChapterAttentionMixture.multiHead_isProb
import Mathlib
import Definitions.Def_ChapterAttentionMixture
import Theorems.Thm_BookProof_ChapterAttentionMixture_mixture_isProb
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_nonneg
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterAttentionMixture



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {w : Fin H → ℝ} (hw0 : ∀ h, 0 ≤ w h) (hw : ∑ h, w h = 1)
    (beta : Fin H → ℝ) (s : Fin H → Fin m → ℝ) (j₀ : Fin m) :
    (∀ j, 0 ≤ multiHead w beta s j) ∧ ∑ j, multiHead w beta s j = 1 :=
  mixture_isProb hw0 hw (fun h j => scoreSoftmax_nonneg (beta h) (s h) j)
      (fun h => scoreSoftmax_sum_one (beta h) (s h) j₀)
