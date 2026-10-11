-- Prove2me | solution 1 for BookProof.ChapterAttentionMixture.le_shannonEntropy_multiHead
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:45:12.992134+00:00
-- url     : https://prove2.me/submissions/e31df906-1b1e-43b4-874a-e3dd69322bad

-- Generated from ChapterAttentionMixture.lean — solution of BookProof.ChapterAttentionMixture.le_shannonEntropy_multiHead
import Mathlib
import Definitions.Def_ChapterAttentionMixture
import Theorems.Thm_BookProof_ChapterAttentionMixture_le_shannonEntropy_mixture
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_nonneg
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterAttentionEntropy
open BookProof.ChapterAttentionMixture



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {w : Fin H → ℝ} (hw0 : ∀ h, 0 ≤ w h) (hw : ∑ h, w h = 1)
    (beta : Fin H → ℝ) (s : Fin H → Fin m → ℝ) :
    ∑ h, w h * shannonEntropy (scoreSoftmax (beta h) (s h))
      ≤ shannonEntropy (multiHead w beta s) := le_shannonEntropy_mixture hw0 hw (fun h j => scoreSoftmax_nonneg (beta h) (s h) j)
