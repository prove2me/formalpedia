-- Prove2me | solution 1 for BookProof.ChapterAttentionMixture.le_shannonEntropy_mixture
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:28:43.498177+00:00
-- url     : https://prove2.me/submissions/de37cfc8-9c4c-4562-a5fa-ca804b9e4fff

-- Generated from ChapterAttentionMixture.lean — solution of BookProof.ChapterAttentionMixture.le_shannonEntropy_mixture
import Mathlib
import Definitions.Def_ChapterAttentionMixture
import Theorems.Thm_BookProof_ChapterAttentionMixture_shannonEntropy_eq_sum_negMulLog
import Theorems.Thm_BookProof_ChapterAttentionMixture_le_negMulLog_mixture
import Definitions.Def_ChapterAttentionEntropy
open BookProof.ChapterAttentionEntropy
open BookProof.ChapterAttentionMixture



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {w : Fin H → ℝ} {p : Fin H → Fin m → ℝ}
    (hw0 : ∀ h, 0 ≤ w h) (hw : ∑ h, w h = 1) (hp0 : ∀ h j, 0 ≤ p h j) :
    ∑ h, w h * shannonEntropy (p h) ≤ shannonEntropy (mixture w p) := by

  have hleft : ∑ h, w h * shannonEntropy (p h)
      = ∑ j, ∑ h, w h * Real.negMulLog (p h j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [shannonEntropy_eq_sum_negMulLog, Finset.mul_sum]
  rw [hleft, shannonEntropy_eq_sum_negMulLog]
  exact Finset.sum_le_sum fun j _ => le_negMulLog_mixture hw0 hw hp0 j
